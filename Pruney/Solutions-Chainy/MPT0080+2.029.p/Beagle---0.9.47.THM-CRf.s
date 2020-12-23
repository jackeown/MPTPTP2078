%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:53 EST 2020

% Result     : Theorem 9.38s
% Output     : CNFRefutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 118 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 132 expanded)
%              Number of equality atoms :   41 (  79 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_190,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_198,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190,c_26])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_204,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_223,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_204])).

tff(c_253,plain,(
    ! [A_49,B_50] : k2_xboole_0(A_49,k4_xboole_0(B_50,A_49)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_283,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_253])).

tff(c_291,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_283])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    ! [A_28,B_27] : r1_tarski(A_28,k2_xboole_0(B_27,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_24])).

tff(c_221,plain,(
    ! [A_28,B_27] : k4_xboole_0(A_28,k2_xboole_0(B_27,A_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_204])).

tff(c_16,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_493,plain,(
    ! [A_55,B_56] : k4_xboole_0(k2_xboole_0(A_55,B_56),B_56) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_499,plain,(
    ! [B_56,A_55] : k2_xboole_0(B_56,k4_xboole_0(A_55,B_56)) = k2_xboole_0(B_56,k2_xboole_0(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_16])).

tff(c_1124,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,k2_xboole_0(A_84,B_83)) = k2_xboole_0(B_83,A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_499])).

tff(c_1148,plain,(
    ! [B_83,A_84] : k4_xboole_0(k2_xboole_0(B_83,A_84),k2_xboole_0(A_84,B_83)) = k4_xboole_0(B_83,k2_xboole_0(A_84,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_18])).

tff(c_1204,plain,(
    ! [B_83,A_84] : k4_xboole_0(k2_xboole_0(B_83,A_84),k2_xboole_0(A_84,B_83)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_1148])).

tff(c_674,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1879,plain,(
    ! [C_109,A_110,B_111] : k2_xboole_0(C_109,k4_xboole_0(A_110,k2_xboole_0(B_111,C_109))) = k2_xboole_0(C_109,k4_xboole_0(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_16])).

tff(c_1952,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,k4_xboole_0(k2_xboole_0(B_83,A_84),A_84)) = k2_xboole_0(B_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_1879])).

tff(c_2043,plain,(
    ! [B_112,A_113] : k2_xboole_0(B_112,k4_xboole_0(B_112,A_113)) = B_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_18,c_1952])).

tff(c_2193,plain,(
    ! [B_114,A_115] : r1_tarski(k4_xboole_0(B_114,A_115),B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2043,c_61])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_560,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(A_58,C_59)
      | ~ r1_xboole_0(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_612,plain,(
    ! [A_62] :
      ( r1_xboole_0(A_62,'#skF_3')
      | ~ r1_tarski(A_62,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_560])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_619,plain,(
    ! [A_62] :
      ( k3_xboole_0(A_62,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_62,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_612,c_4])).

tff(c_2248,plain,(
    ! [A_115] : k3_xboole_0(k4_xboole_0('#skF_1',A_115),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2193,c_619])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_31,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_222,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31,c_204])).

tff(c_20762,plain,(
    ! [B_298,A_299,A_300] : k2_xboole_0(B_298,k4_xboole_0(A_299,k2_xboole_0(B_298,A_300))) = k2_xboole_0(B_298,k4_xboole_0(A_299,A_300)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1879])).

tff(c_21259,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_20762])).

tff(c_21401,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_21259])).

tff(c_99,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    ! [A_28,B_27] : k3_xboole_0(A_28,k2_xboole_0(B_27,A_28)) = A_28 ),
    inference(resolution,[status(thm)],[c_61,c_99])).

tff(c_21608,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_21401,c_112])).

tff(c_21679,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2248,c_21608])).

tff(c_21681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_21679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:37:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.38/3.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.38/3.66  
% 9.38/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.38/3.66  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.38/3.66  
% 9.38/3.66  %Foreground sorts:
% 9.38/3.66  
% 9.38/3.66  
% 9.38/3.66  %Background operators:
% 9.38/3.66  
% 9.38/3.66  
% 9.38/3.66  %Foreground operators:
% 9.38/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.38/3.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.38/3.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.38/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.38/3.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.38/3.66  tff('#skF_2', type, '#skF_2': $i).
% 9.38/3.66  tff('#skF_3', type, '#skF_3': $i).
% 9.38/3.66  tff('#skF_1', type, '#skF_1': $i).
% 9.38/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.38/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.38/3.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.38/3.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.38/3.66  
% 9.49/3.68  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.49/3.68  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 9.49/3.68  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.49/3.68  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.49/3.68  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.49/3.68  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 9.49/3.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.49/3.68  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.49/3.68  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 9.49/3.68  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.49/3.68  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.49/3.68  tff(c_190, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | k4_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.49/3.68  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.49/3.68  tff(c_198, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_190, c_26])).
% 9.49/3.68  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.49/3.68  tff(c_41, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.49/3.68  tff(c_44, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 9.49/3.68  tff(c_204, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.49/3.68  tff(c_223, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_204])).
% 9.49/3.68  tff(c_253, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k4_xboole_0(B_50, A_49))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.49/3.68  tff(c_283, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_223, c_253])).
% 9.49/3.68  tff(c_291, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_283])).
% 9.49/3.68  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.49/3.68  tff(c_46, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.49/3.68  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.49/3.68  tff(c_61, plain, (![A_28, B_27]: (r1_tarski(A_28, k2_xboole_0(B_27, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_24])).
% 9.49/3.68  tff(c_221, plain, (![A_28, B_27]: (k4_xboole_0(A_28, k2_xboole_0(B_27, A_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_204])).
% 9.49/3.68  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.49/3.68  tff(c_493, plain, (![A_55, B_56]: (k4_xboole_0(k2_xboole_0(A_55, B_56), B_56)=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.49/3.68  tff(c_499, plain, (![B_56, A_55]: (k2_xboole_0(B_56, k4_xboole_0(A_55, B_56))=k2_xboole_0(B_56, k2_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_493, c_16])).
% 9.49/3.68  tff(c_1124, plain, (![B_83, A_84]: (k2_xboole_0(B_83, k2_xboole_0(A_84, B_83))=k2_xboole_0(B_83, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_499])).
% 9.49/3.68  tff(c_1148, plain, (![B_83, A_84]: (k4_xboole_0(k2_xboole_0(B_83, A_84), k2_xboole_0(A_84, B_83))=k4_xboole_0(B_83, k2_xboole_0(A_84, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_1124, c_18])).
% 9.49/3.68  tff(c_1204, plain, (![B_83, A_84]: (k4_xboole_0(k2_xboole_0(B_83, A_84), k2_xboole_0(A_84, B_83))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_1148])).
% 9.49/3.68  tff(c_674, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.49/3.68  tff(c_1879, plain, (![C_109, A_110, B_111]: (k2_xboole_0(C_109, k4_xboole_0(A_110, k2_xboole_0(B_111, C_109)))=k2_xboole_0(C_109, k4_xboole_0(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_674, c_16])).
% 9.49/3.68  tff(c_1952, plain, (![B_83, A_84]: (k2_xboole_0(B_83, k4_xboole_0(k2_xboole_0(B_83, A_84), A_84))=k2_xboole_0(B_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1204, c_1879])).
% 9.49/3.68  tff(c_2043, plain, (![B_112, A_113]: (k2_xboole_0(B_112, k4_xboole_0(B_112, A_113))=B_112)), inference(demodulation, [status(thm), theory('equality')], [c_291, c_18, c_1952])).
% 9.49/3.68  tff(c_2193, plain, (![B_114, A_115]: (r1_tarski(k4_xboole_0(B_114, A_115), B_114))), inference(superposition, [status(thm), theory('equality')], [c_2043, c_61])).
% 9.49/3.68  tff(c_28, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.49/3.68  tff(c_560, plain, (![A_58, C_59, B_60]: (r1_xboole_0(A_58, C_59) | ~r1_xboole_0(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.49/3.68  tff(c_612, plain, (![A_62]: (r1_xboole_0(A_62, '#skF_3') | ~r1_tarski(A_62, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_560])).
% 9.49/3.68  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.49/3.68  tff(c_619, plain, (![A_62]: (k3_xboole_0(A_62, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_62, '#skF_1'))), inference(resolution, [status(thm)], [c_612, c_4])).
% 9.49/3.68  tff(c_2248, plain, (![A_115]: (k3_xboole_0(k4_xboole_0('#skF_1', A_115), '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2193, c_619])).
% 9.49/3.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.49/3.68  tff(c_30, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.49/3.68  tff(c_31, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 9.49/3.68  tff(c_222, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_31, c_204])).
% 9.49/3.68  tff(c_20762, plain, (![B_298, A_299, A_300]: (k2_xboole_0(B_298, k4_xboole_0(A_299, k2_xboole_0(B_298, A_300)))=k2_xboole_0(B_298, k4_xboole_0(A_299, A_300)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1879])).
% 9.49/3.68  tff(c_21259, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_222, c_20762])).
% 9.49/3.68  tff(c_21401, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_291, c_21259])).
% 9.49/3.68  tff(c_99, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.49/3.68  tff(c_112, plain, (![A_28, B_27]: (k3_xboole_0(A_28, k2_xboole_0(B_27, A_28))=A_28)), inference(resolution, [status(thm)], [c_61, c_99])).
% 9.49/3.68  tff(c_21608, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_21401, c_112])).
% 9.49/3.68  tff(c_21679, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2248, c_21608])).
% 9.49/3.68  tff(c_21681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_21679])).
% 9.49/3.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.68  
% 9.49/3.68  Inference rules
% 9.49/3.68  ----------------------
% 9.49/3.68  #Ref     : 0
% 9.49/3.68  #Sup     : 5454
% 9.49/3.68  #Fact    : 0
% 9.49/3.68  #Define  : 0
% 9.49/3.68  #Split   : 6
% 9.49/3.68  #Chain   : 0
% 9.49/3.68  #Close   : 0
% 9.49/3.68  
% 9.49/3.68  Ordering : KBO
% 9.49/3.68  
% 9.49/3.68  Simplification rules
% 9.49/3.68  ----------------------
% 9.49/3.68  #Subsume      : 599
% 9.49/3.68  #Demod        : 5887
% 9.49/3.68  #Tautology    : 3471
% 9.49/3.68  #SimpNegUnit  : 6
% 9.49/3.68  #BackRed      : 0
% 9.49/3.68  
% 9.49/3.68  #Partial instantiations: 0
% 9.49/3.68  #Strategies tried      : 1
% 9.49/3.68  
% 9.49/3.68  Timing (in seconds)
% 9.49/3.68  ----------------------
% 9.49/3.68  Preprocessing        : 0.28
% 9.49/3.68  Parsing              : 0.16
% 9.49/3.68  CNF conversion       : 0.02
% 9.49/3.68  Main loop            : 2.65
% 9.49/3.68  Inferencing          : 0.54
% 9.49/3.68  Reduction            : 1.52
% 9.49/3.68  Demodulation         : 1.33
% 9.49/3.68  BG Simplification    : 0.06
% 9.49/3.68  Subsumption          : 0.41
% 9.49/3.68  Abstraction          : 0.10
% 9.49/3.68  MUC search           : 0.00
% 9.49/3.69  Cooper               : 0.00
% 9.49/3.69  Total                : 2.96
% 9.49/3.69  Index Insertion      : 0.00
% 9.49/3.69  Index Deletion       : 0.00
% 9.49/3.69  Index Matching       : 0.00
% 9.49/3.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
