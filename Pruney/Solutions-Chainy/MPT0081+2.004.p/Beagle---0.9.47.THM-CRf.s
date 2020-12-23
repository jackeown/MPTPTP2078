%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:57 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   57 (  96 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   50 (  91 expanded)
%              Number of equality atoms :   41 (  79 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_191,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_170])).

tff(c_198,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_191])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_170])).

tff(c_194,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_139,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_350,plain,(
    ! [B_32,A_33] : k4_xboole_0(B_32,k3_xboole_0(A_33,B_32)) = k4_xboole_0(B_32,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_373,plain,(
    ! [A_9,B_10] : k4_xboole_0(k4_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = k4_xboole_0(k4_xboole_0(A_9,B_10),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_350])).

tff(c_427,plain,(
    ! [A_34,B_35] : k4_xboole_0(k4_xboole_0(A_34,B_35),A_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_373])).

tff(c_462,plain,(
    ! [A_9,B_10] : k4_xboole_0(k3_xboole_0(A_9,B_10),A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_427])).

tff(c_38,plain,(
    ! [B_16,A_17] : k3_xboole_0(B_16,A_17) = k3_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_17] : k3_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_151,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_139])).

tff(c_164,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_151])).

tff(c_546,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k4_xboole_0(A_38,B_39),k3_xboole_0(A_38,C_40)) = k4_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_603,plain,(
    ! [A_6,C_40] : k4_xboole_0(A_6,k4_xboole_0(k1_xboole_0,C_40)) = k2_xboole_0(A_6,k3_xboole_0(A_6,C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_546])).

tff(c_618,plain,(
    ! [A_41,C_42] : k2_xboole_0(A_41,k3_xboole_0(A_41,C_42)) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_164,c_603])).

tff(c_645,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_618])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_85])).

tff(c_588,plain,(
    ! [B_39] : k4_xboole_0('#skF_1',k4_xboole_0(B_39,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_1',B_39),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_546])).

tff(c_944,plain,(
    ! [B_53] : k4_xboole_0('#skF_1',k4_xboole_0(B_53,'#skF_2')) = k4_xboole_0('#skF_1',B_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_588])).

tff(c_977,plain,(
    ! [B_10] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_10)) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_944])).

tff(c_1012,plain,(
    ! [B_54] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_54)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_977])).

tff(c_1033,plain,(
    ! [B_54] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_54)) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_14])).

tff(c_1274,plain,(
    ! [B_58] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_58)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1033])).

tff(c_1318,plain,(
    ! [B_2] : k3_xboole_0('#skF_1',k3_xboole_0(B_2,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1274])).

tff(c_128,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_136,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128,c_21])).

tff(c_2026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.50  
% 3.25/1.50  %Foreground sorts:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Background operators:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Foreground operators:
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.50  
% 3.25/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.25/1.51  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.25/1.51  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.25/1.51  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.25/1.51  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.25/1.51  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.25/1.51  tff(f_48, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.25/1.51  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.25/1.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.51  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.51  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.51  tff(c_170, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.51  tff(c_191, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_170])).
% 3.25/1.51  tff(c_198, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_191])).
% 3.25/1.51  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.51  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.51  tff(c_179, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_170])).
% 3.25/1.51  tff(c_194, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 3.25/1.51  tff(c_139, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.51  tff(c_350, plain, (![B_32, A_33]: (k4_xboole_0(B_32, k3_xboole_0(A_33, B_32))=k4_xboole_0(B_32, A_33))), inference(superposition, [status(thm), theory('equality')], [c_2, c_139])).
% 3.25/1.51  tff(c_373, plain, (![A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=k4_xboole_0(k4_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_194, c_350])).
% 3.25/1.51  tff(c_427, plain, (![A_34, B_35]: (k4_xboole_0(k4_xboole_0(A_34, B_35), A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_373])).
% 3.25/1.51  tff(c_462, plain, (![A_9, B_10]: (k4_xboole_0(k3_xboole_0(A_9, B_10), A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_427])).
% 3.25/1.51  tff(c_38, plain, (![B_16, A_17]: (k3_xboole_0(B_16, A_17)=k3_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.51  tff(c_54, plain, (![A_17]: (k3_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 3.25/1.51  tff(c_151, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_17))), inference(superposition, [status(thm), theory('equality')], [c_54, c_139])).
% 3.25/1.51  tff(c_164, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_151])).
% 3.25/1.51  tff(c_546, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k4_xboole_0(A_38, B_39), k3_xboole_0(A_38, C_40))=k4_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.51  tff(c_603, plain, (![A_6, C_40]: (k4_xboole_0(A_6, k4_xboole_0(k1_xboole_0, C_40))=k2_xboole_0(A_6, k3_xboole_0(A_6, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_546])).
% 3.25/1.51  tff(c_618, plain, (![A_41, C_42]: (k2_xboole_0(A_41, k3_xboole_0(A_41, C_42))=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_164, c_603])).
% 3.25/1.51  tff(c_645, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_618])).
% 3.25/1.51  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.51  tff(c_85, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.51  tff(c_89, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_85])).
% 3.25/1.51  tff(c_588, plain, (![B_39]: (k4_xboole_0('#skF_1', k4_xboole_0(B_39, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_1', B_39), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_89, c_546])).
% 3.25/1.51  tff(c_944, plain, (![B_53]: (k4_xboole_0('#skF_1', k4_xboole_0(B_53, '#skF_2'))=k4_xboole_0('#skF_1', B_53))), inference(demodulation, [status(thm), theory('equality')], [c_645, c_588])).
% 3.25/1.51  tff(c_977, plain, (![B_10]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_10))=k4_xboole_0('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_462, c_944])).
% 3.25/1.51  tff(c_1012, plain, (![B_54]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_54))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_977])).
% 3.25/1.51  tff(c_1033, plain, (![B_54]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_54))=k4_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1012, c_14])).
% 3.25/1.51  tff(c_1274, plain, (![B_58]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_58))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1033])).
% 3.25/1.51  tff(c_1318, plain, (![B_2]: (k3_xboole_0('#skF_1', k3_xboole_0(B_2, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1274])).
% 3.25/1.51  tff(c_128, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.51  tff(c_20, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.51  tff(c_21, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 3.25/1.51  tff(c_136, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_128, c_21])).
% 3.25/1.51  tff(c_2026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1318, c_136])).
% 3.25/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  Inference rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Ref     : 0
% 3.25/1.51  #Sup     : 497
% 3.25/1.51  #Fact    : 0
% 3.25/1.51  #Define  : 0
% 3.25/1.51  #Split   : 0
% 3.25/1.51  #Chain   : 0
% 3.25/1.51  #Close   : 0
% 3.25/1.51  
% 3.25/1.51  Ordering : KBO
% 3.25/1.51  
% 3.25/1.51  Simplification rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Subsume      : 0
% 3.25/1.51  #Demod        : 423
% 3.25/1.51  #Tautology    : 395
% 3.25/1.51  #SimpNegUnit  : 0
% 3.25/1.51  #BackRed      : 1
% 3.25/1.51  
% 3.25/1.51  #Partial instantiations: 0
% 3.25/1.51  #Strategies tried      : 1
% 3.25/1.51  
% 3.25/1.51  Timing (in seconds)
% 3.25/1.51  ----------------------
% 3.25/1.52  Preprocessing        : 0.26
% 3.25/1.52  Parsing              : 0.15
% 3.25/1.52  CNF conversion       : 0.02
% 3.25/1.52  Main loop            : 0.48
% 3.25/1.52  Inferencing          : 0.16
% 3.25/1.52  Reduction            : 0.22
% 3.25/1.52  Demodulation         : 0.18
% 3.25/1.52  BG Simplification    : 0.02
% 3.25/1.52  Subsumption          : 0.06
% 3.25/1.52  Abstraction          : 0.02
% 3.25/1.52  MUC search           : 0.00
% 3.25/1.52  Cooper               : 0.00
% 3.25/1.52  Total                : 0.78
% 3.25/1.52  Index Insertion      : 0.00
% 3.25/1.52  Index Deletion       : 0.00
% 3.25/1.52  Index Matching       : 0.00
% 3.25/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
