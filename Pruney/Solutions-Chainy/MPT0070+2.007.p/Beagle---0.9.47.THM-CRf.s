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
% DateTime   : Thu Dec  3 09:43:18 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 108 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :   59 ( 112 expanded)
%              Number of equality atoms :   45 (  85 expanded)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_165,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_169,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_24])).

tff(c_202,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_235,plain,(
    ! [B_39] : k3_xboole_0(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_22])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_247,plain,(
    ! [B_39] : k3_xboole_0(B_39,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_4])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_151,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_224,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_202])).

tff(c_410,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_224])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_170,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_170])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1027,plain,(
    ! [A_68,B_69] : k3_xboole_0(k4_xboole_0(A_68,B_69),A_68) = k4_xboole_0(A_68,B_69) ),
    inference(resolution,[status(thm)],[c_14,c_139])).

tff(c_1084,plain,(
    ! [B_4,B_69] : k3_xboole_0(B_4,k4_xboole_0(B_4,B_69)) = k4_xboole_0(B_4,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1027])).

tff(c_205,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,k4_xboole_0(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_20])).

tff(c_1875,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_205])).

tff(c_1947,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_1875])).

tff(c_1985,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1947])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2678,plain,(
    ! [C_100] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_100)) = k4_xboole_0('#skF_2',C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_1985,c_18])).

tff(c_15209,plain,(
    ! [B_280] : k4_xboole_0('#skF_2',k2_xboole_0(B_280,'#skF_3')) = k4_xboole_0('#skF_2',B_280) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2678])).

tff(c_267,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),C_42) = k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_276,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),k4_xboole_0(A_40,k2_xboole_0(B_41,C_42))) = k3_xboole_0(k4_xboole_0(A_40,B_41),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_20])).

tff(c_15257,plain,(
    ! [B_280] : k4_xboole_0(k4_xboole_0('#skF_2',B_280),k4_xboole_0('#skF_2',B_280)) = k3_xboole_0(k4_xboole_0('#skF_2',B_280),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15209,c_276])).

tff(c_15374,plain,(
    ! [B_281] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',B_281)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_4,c_15257])).

tff(c_15734,plain,(
    ! [B_283] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_283)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_15374])).

tff(c_16294,plain,(
    ! [A_286] : k3_xboole_0('#skF_3',k3_xboole_0(A_286,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_15734])).

tff(c_16437,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_16294])).

tff(c_1080,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(k3_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1027])).

tff(c_8868,plain,(
    ! [A_228,B_229] : k3_xboole_0(A_228,k3_xboole_0(A_228,B_229)) = k3_xboole_0(A_228,B_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_1080])).

tff(c_9068,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k3_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8868])).

tff(c_16500,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16437,c_9068])).

tff(c_16600,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_16500])).

tff(c_16602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_16600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.08/2.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.94  
% 8.08/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.94  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.08/2.94  
% 8.08/2.94  %Foreground sorts:
% 8.08/2.94  
% 8.08/2.94  
% 8.08/2.94  %Background operators:
% 8.08/2.94  
% 8.08/2.94  
% 8.08/2.94  %Foreground operators:
% 8.08/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.08/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.08/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.08/2.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.08/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.08/2.94  tff('#skF_3', type, '#skF_3': $i).
% 8.08/2.94  tff('#skF_1', type, '#skF_1': $i).
% 8.08/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.08/2.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.08/2.94  
% 8.08/2.96  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.08/2.96  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 8.08/2.96  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.08/2.96  tff(f_49, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 8.08/2.96  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.08/2.96  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.08/2.96  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.08/2.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.08/2.96  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.08/2.96  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.08/2.96  tff(c_165, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.08/2.96  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.08/2.96  tff(c_169, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_165, c_24])).
% 8.08/2.96  tff(c_202, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.08/2.96  tff(c_22, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.08/2.96  tff(c_235, plain, (![B_39]: (k3_xboole_0(k1_xboole_0, B_39)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_202, c_22])).
% 8.08/2.96  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.08/2.96  tff(c_247, plain, (![B_39]: (k3_xboole_0(B_39, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_235, c_4])).
% 8.08/2.96  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.08/2.96  tff(c_139, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.08/2.96  tff(c_151, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_28, c_139])).
% 8.08/2.96  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.08/2.96  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.08/2.96  tff(c_224, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_202])).
% 8.08/2.96  tff(c_410, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_224])).
% 8.08/2.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.08/2.96  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.08/2.96  tff(c_170, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.08/2.96  tff(c_178, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_170])).
% 8.08/2.96  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.96  tff(c_1027, plain, (![A_68, B_69]: (k3_xboole_0(k4_xboole_0(A_68, B_69), A_68)=k4_xboole_0(A_68, B_69))), inference(resolution, [status(thm)], [c_14, c_139])).
% 8.08/2.96  tff(c_1084, plain, (![B_4, B_69]: (k3_xboole_0(B_4, k4_xboole_0(B_4, B_69))=k4_xboole_0(B_4, B_69))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1027])).
% 8.08/2.96  tff(c_205, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k3_xboole_0(A_37, k4_xboole_0(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_20])).
% 8.08/2.96  tff(c_1875, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_205])).
% 8.08/2.96  tff(c_1947, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_1875])).
% 8.08/2.96  tff(c_1985, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1947])).
% 8.08/2.96  tff(c_18, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.08/2.96  tff(c_2678, plain, (![C_100]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_100))=k4_xboole_0('#skF_2', C_100))), inference(superposition, [status(thm), theory('equality')], [c_1985, c_18])).
% 8.08/2.96  tff(c_15209, plain, (![B_280]: (k4_xboole_0('#skF_2', k2_xboole_0(B_280, '#skF_3'))=k4_xboole_0('#skF_2', B_280))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2678])).
% 8.08/2.96  tff(c_267, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), C_42)=k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.08/2.96  tff(c_276, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))=k3_xboole_0(k4_xboole_0(A_40, B_41), C_42))), inference(superposition, [status(thm), theory('equality')], [c_267, c_20])).
% 8.08/2.96  tff(c_15257, plain, (![B_280]: (k4_xboole_0(k4_xboole_0('#skF_2', B_280), k4_xboole_0('#skF_2', B_280))=k3_xboole_0(k4_xboole_0('#skF_2', B_280), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15209, c_276])).
% 8.08/2.96  tff(c_15374, plain, (![B_281]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', B_281))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_410, c_4, c_15257])).
% 8.08/2.96  tff(c_15734, plain, (![B_283]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_283))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_15374])).
% 8.08/2.96  tff(c_16294, plain, (![A_286]: (k3_xboole_0('#skF_3', k3_xboole_0(A_286, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_15734])).
% 8.08/2.96  tff(c_16437, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_151, c_16294])).
% 8.08/2.96  tff(c_1080, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(k3_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1027])).
% 8.08/2.96  tff(c_8868, plain, (![A_228, B_229]: (k3_xboole_0(A_228, k3_xboole_0(A_228, B_229))=k3_xboole_0(A_228, B_229))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_1080])).
% 8.08/2.96  tff(c_9068, plain, (![B_4, A_3]: (k3_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k3_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8868])).
% 8.08/2.96  tff(c_16500, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16437, c_9068])).
% 8.08/2.96  tff(c_16600, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_247, c_16500])).
% 8.08/2.96  tff(c_16602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_16600])).
% 8.08/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.96  
% 8.08/2.96  Inference rules
% 8.08/2.96  ----------------------
% 8.08/2.96  #Ref     : 0
% 8.08/2.96  #Sup     : 3980
% 8.08/2.96  #Fact    : 0
% 8.08/2.96  #Define  : 0
% 8.08/2.96  #Split   : 0
% 8.08/2.96  #Chain   : 0
% 8.08/2.96  #Close   : 0
% 8.08/2.96  
% 8.08/2.96  Ordering : KBO
% 8.08/2.96  
% 8.08/2.96  Simplification rules
% 8.08/2.96  ----------------------
% 8.08/2.96  #Subsume      : 8
% 8.08/2.96  #Demod        : 4547
% 8.08/2.96  #Tautology    : 3087
% 8.08/2.96  #SimpNegUnit  : 1
% 8.08/2.96  #BackRed      : 4
% 8.08/2.96  
% 8.08/2.96  #Partial instantiations: 0
% 8.08/2.96  #Strategies tried      : 1
% 8.08/2.96  
% 8.08/2.96  Timing (in seconds)
% 8.08/2.96  ----------------------
% 8.08/2.96  Preprocessing        : 0.27
% 8.08/2.96  Parsing              : 0.16
% 8.08/2.96  CNF conversion       : 0.02
% 8.08/2.96  Main loop            : 1.93
% 8.08/2.96  Inferencing          : 0.44
% 8.08/2.96  Reduction            : 1.06
% 8.08/2.96  Demodulation         : 0.93
% 8.08/2.96  BG Simplification    : 0.05
% 8.08/2.96  Subsumption          : 0.28
% 8.08/2.96  Abstraction          : 0.07
% 8.08/2.96  MUC search           : 0.00
% 8.08/2.96  Cooper               : 0.00
% 8.08/2.96  Total                : 2.24
% 8.08/2.96  Index Insertion      : 0.00
% 8.08/2.96  Index Deletion       : 0.00
% 8.08/2.96  Index Matching       : 0.00
% 8.08/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
