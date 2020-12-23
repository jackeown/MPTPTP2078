%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:58 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   56 (  95 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   52 (  97 expanded)
%              Number of equality atoms :   36 (  70 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_25,B_26] : k3_xboole_0(A_25,k2_xboole_0(A_25,B_26)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_132,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_10])).

tff(c_165,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_159])).

tff(c_6,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_261,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k4_xboole_0(A_46,B_47),C_48) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_584,plain,(
    ! [C_57,A_58,B_59] :
      ( k1_xboole_0 = C_57
      | ~ r1_tarski(C_57,k4_xboole_0(A_58,k2_xboole_0(B_59,C_57))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_12])).

tff(c_612,plain,(
    ! [B_60,A_61] :
      ( k1_xboole_0 = B_60
      | ~ r1_tarski(B_60,k4_xboole_0(A_61,A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_584])).

tff(c_634,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_612])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_711,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_612])).

tff(c_742,plain,(
    ! [A_65] : k4_xboole_0(A_65,k1_xboole_0) = k3_xboole_0(A_65,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_18])).

tff(c_758,plain,(
    ! [A_65] : k4_xboole_0(A_65,k1_xboole_0) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_742])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_121,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_106])).

tff(c_875,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_121])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k4_xboole_0(A_18,B_19),k3_xboole_0(A_18,C_20)) = k4_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_982,plain,(
    ! [C_20] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_20)) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_20])).

tff(c_1508,plain,(
    ! [C_81] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_81)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_982])).

tff(c_1714,plain,(
    ! [B_85] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_85)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1508])).

tff(c_1740,plain,(
    ! [B_85] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_85)) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_18])).

tff(c_1776,plain,(
    ! [B_85] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_85)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_1740])).

tff(c_50,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_24])).

tff(c_1927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:35:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.59  
% 3.38/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.60  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.38/1.60  
% 3.38/1.60  %Foreground sorts:
% 3.38/1.60  
% 3.38/1.60  
% 3.38/1.60  %Background operators:
% 3.38/1.60  
% 3.38/1.60  
% 3.38/1.60  %Foreground operators:
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.60  
% 3.77/1.61  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.77/1.61  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.77/1.61  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.77/1.61  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.77/1.61  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.77/1.61  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.77/1.61  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.77/1.61  tff(f_54, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.77/1.61  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.77/1.61  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.77/1.61  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.77/1.61  tff(c_35, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k2_xboole_0(A_25, B_26))=A_25)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.61  tff(c_47, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_35])).
% 3.77/1.61  tff(c_132, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.77/1.61  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.61  tff(c_159, plain, (![A_39, B_40]: (r1_tarski(k3_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_132, c_10])).
% 3.77/1.61  tff(c_165, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_47, c_159])).
% 3.77/1.61  tff(c_6, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.61  tff(c_106, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.77/1.61  tff(c_127, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_106])).
% 3.77/1.61  tff(c_261, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k4_xboole_0(A_46, B_47), C_48)=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.77/1.61  tff(c_12, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.61  tff(c_584, plain, (![C_57, A_58, B_59]: (k1_xboole_0=C_57 | ~r1_tarski(C_57, k4_xboole_0(A_58, k2_xboole_0(B_59, C_57))))), inference(superposition, [status(thm), theory('equality')], [c_261, c_12])).
% 3.77/1.61  tff(c_612, plain, (![B_60, A_61]: (k1_xboole_0=B_60 | ~r1_tarski(B_60, k4_xboole_0(A_61, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_584])).
% 3.77/1.61  tff(c_634, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_165, c_612])).
% 3.77/1.61  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.77/1.61  tff(c_711, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_165, c_612])).
% 3.77/1.61  tff(c_742, plain, (![A_65]: (k4_xboole_0(A_65, k1_xboole_0)=k3_xboole_0(A_65, A_65))), inference(superposition, [status(thm), theory('equality')], [c_711, c_18])).
% 3.77/1.61  tff(c_758, plain, (![A_65]: (k4_xboole_0(A_65, k1_xboole_0)=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_742])).
% 3.77/1.61  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.77/1.61  tff(c_81, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.61  tff(c_89, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_81])).
% 3.77/1.61  tff(c_121, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_106])).
% 3.77/1.61  tff(c_875, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_758, c_121])).
% 3.77/1.61  tff(c_20, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k4_xboole_0(A_18, B_19), k3_xboole_0(A_18, C_20))=k4_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.77/1.61  tff(c_982, plain, (![C_20]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_20))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_20)))), inference(superposition, [status(thm), theory('equality')], [c_875, c_20])).
% 3.77/1.61  tff(c_1508, plain, (![C_81]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_81))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_982])).
% 3.77/1.61  tff(c_1714, plain, (![B_85]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_85))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1508])).
% 3.77/1.61  tff(c_1740, plain, (![B_85]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_85))=k4_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1714, c_18])).
% 3.77/1.61  tff(c_1776, plain, (![B_85]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_85))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_634, c_1740])).
% 3.77/1.61  tff(c_50, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.61  tff(c_24, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.77/1.61  tff(c_54, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_24])).
% 3.77/1.61  tff(c_1927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1776, c_54])).
% 3.77/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.61  
% 3.77/1.61  Inference rules
% 3.77/1.61  ----------------------
% 3.77/1.61  #Ref     : 0
% 3.77/1.61  #Sup     : 464
% 3.77/1.61  #Fact    : 0
% 3.77/1.61  #Define  : 0
% 3.77/1.61  #Split   : 1
% 3.77/1.61  #Chain   : 0
% 3.77/1.61  #Close   : 0
% 3.77/1.61  
% 3.77/1.61  Ordering : KBO
% 3.77/1.61  
% 3.77/1.61  Simplification rules
% 3.77/1.61  ----------------------
% 3.77/1.61  #Subsume      : 25
% 3.77/1.61  #Demod        : 400
% 3.77/1.61  #Tautology    : 290
% 3.77/1.61  #SimpNegUnit  : 0
% 3.77/1.61  #BackRed      : 6
% 3.77/1.61  
% 3.77/1.61  #Partial instantiations: 0
% 3.77/1.61  #Strategies tried      : 1
% 3.77/1.61  
% 3.77/1.61  Timing (in seconds)
% 3.77/1.61  ----------------------
% 3.77/1.61  Preprocessing        : 0.30
% 3.77/1.61  Parsing              : 0.17
% 3.77/1.61  CNF conversion       : 0.02
% 3.77/1.61  Main loop            : 0.55
% 3.77/1.61  Inferencing          : 0.19
% 3.77/1.61  Reduction            : 0.21
% 3.77/1.61  Demodulation         : 0.17
% 3.77/1.61  BG Simplification    : 0.02
% 3.77/1.61  Subsumption          : 0.08
% 3.77/1.61  Abstraction          : 0.03
% 3.77/1.62  MUC search           : 0.00
% 3.77/1.62  Cooper               : 0.00
% 3.77/1.62  Total                : 0.88
% 3.77/1.62  Index Insertion      : 0.00
% 3.77/1.62  Index Deletion       : 0.00
% 3.77/1.62  Index Matching       : 0.00
% 3.77/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
