%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:33 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  62 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k1_relat_1(k6_subset_1(B_10,k7_relat_1(B_10,A_9))) = k6_subset_1(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( k1_relat_1(k4_xboole_0(B_10,k7_relat_1(B_10,A_9))) = k4_xboole_0(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [B_23,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_24)),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [B_23,A_24] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_23,A_24)),k1_relat_1(B_23)) = k1_relat_1(k7_relat_1(B_23,A_24))
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_79,c_6])).

tff(c_197,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k1_relat_1(B_33),k1_relat_1(k7_relat_1(B_33,A_34))) = k1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_501,plain,(
    ! [B_48,A_49] :
      ( k5_xboole_0(k1_relat_1(B_48),k1_relat_1(k7_relat_1(B_48,A_49))) = k4_xboole_0(k1_relat_1(B_48),k1_relat_1(k7_relat_1(B_48,A_49)))
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_4])).

tff(c_113,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(k1_relat_1(B_27),A_28) = k1_relat_1(k7_relat_1(B_27,A_28))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_122,plain,(
    ! [B_27,A_28] :
      ( k5_xboole_0(k1_relat_1(B_27),k1_relat_1(k7_relat_1(B_27,A_28))) = k4_xboole_0(k1_relat_1(B_27),A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_545,plain,(
    ! [B_50,A_51] :
      ( k4_xboole_0(k1_relat_1(B_50),k1_relat_1(k7_relat_1(B_50,A_51))) = k4_xboole_0(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_122])).

tff(c_16,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16])).

tff(c_554,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_19])).

tff(c_581,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_554])).

tff(c_586,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_581])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.34  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.42/1.34  
% 2.42/1.34  %Foreground sorts:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Background operators:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Foreground operators:
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.42/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.34  
% 2.42/1.35  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 2.42/1.35  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.42/1.35  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.42/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.42/1.35  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.42/1.35  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.42/1.35  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.42/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.42/1.35  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.42/1.35  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.35  tff(c_10, plain, (![B_10, A_9]: (k1_relat_1(k6_subset_1(B_10, k7_relat_1(B_10, A_9)))=k6_subset_1(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.35  tff(c_20, plain, (![B_10, A_9]: (k1_relat_1(k4_xboole_0(B_10, k7_relat_1(B_10, A_9)))=k4_xboole_0(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 2.42/1.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.35  tff(c_79, plain, (![B_23, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_24)), k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.35  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.35  tff(c_82, plain, (![B_23, A_24]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_23, A_24)), k1_relat_1(B_23))=k1_relat_1(k7_relat_1(B_23, A_24)) | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_79, c_6])).
% 2.42/1.35  tff(c_197, plain, (![B_33, A_34]: (k3_xboole_0(k1_relat_1(B_33), k1_relat_1(k7_relat_1(B_33, A_34)))=k1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_82])).
% 2.42/1.35  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.35  tff(c_501, plain, (![B_48, A_49]: (k5_xboole_0(k1_relat_1(B_48), k1_relat_1(k7_relat_1(B_48, A_49)))=k4_xboole_0(k1_relat_1(B_48), k1_relat_1(k7_relat_1(B_48, A_49))) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_197, c_4])).
% 2.42/1.35  tff(c_113, plain, (![B_27, A_28]: (k3_xboole_0(k1_relat_1(B_27), A_28)=k1_relat_1(k7_relat_1(B_27, A_28)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.35  tff(c_122, plain, (![B_27, A_28]: (k5_xboole_0(k1_relat_1(B_27), k1_relat_1(k7_relat_1(B_27, A_28)))=k4_xboole_0(k1_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 2.42/1.35  tff(c_545, plain, (![B_50, A_51]: (k4_xboole_0(k1_relat_1(B_50), k1_relat_1(k7_relat_1(B_50, A_51)))=k4_xboole_0(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_501, c_122])).
% 2.42/1.35  tff(c_16, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.42/1.35  tff(c_19, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_16])).
% 2.42/1.35  tff(c_554, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_545, c_19])).
% 2.42/1.35  tff(c_581, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_554])).
% 2.42/1.35  tff(c_586, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_581])).
% 2.42/1.35  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_586])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 158
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 0
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 21
% 2.42/1.35  #Demod        : 13
% 2.42/1.35  #Tautology    : 50
% 2.42/1.35  #SimpNegUnit  : 0
% 2.42/1.35  #BackRed      : 0
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.35  ----------------------
% 2.42/1.35  Preprocessing        : 0.27
% 2.42/1.35  Parsing              : 0.15
% 2.42/1.35  CNF conversion       : 0.01
% 2.42/1.35  Main loop            : 0.27
% 2.42/1.35  Inferencing          : 0.11
% 2.42/1.35  Reduction            : 0.08
% 2.42/1.35  Demodulation         : 0.06
% 2.42/1.35  BG Simplification    : 0.02
% 2.42/1.35  Subsumption          : 0.05
% 2.42/1.35  Abstraction          : 0.02
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.57
% 2.42/1.35  Index Insertion      : 0.00
% 2.42/1.35  Index Deletion       : 0.00
% 2.42/1.35  Index Matching       : 0.00
% 2.42/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
