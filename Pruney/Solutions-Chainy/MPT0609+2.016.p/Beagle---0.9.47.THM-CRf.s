%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:33 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  66 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_19,A_17,B_18] :
      ( k7_relat_1(C_19,k6_subset_1(A_17,B_18)) = k6_subset_1(C_19,k7_relat_1(C_19,B_18))
      | ~ r1_tarski(k1_relat_1(C_19),A_17)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_361,plain,(
    ! [C_51,A_52,B_53] :
      ( k7_relat_1(C_51,k4_xboole_0(A_52,B_53)) = k4_xboole_0(C_51,k7_relat_1(C_51,B_53))
      | ~ r1_tarski(k1_relat_1(C_51),A_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_365,plain,(
    ! [C_51,B_53] :
      ( k7_relat_1(C_51,k4_xboole_0(k1_relat_1(C_51),B_53)) = k4_xboole_0(C_51,k7_relat_1(C_51,B_53))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_8,c_361])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_9,B_10] : k3_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k4_xboole_0(A_9,B_10) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_195,plain,(
    ! [B_43,A_44] :
      ( k3_xboole_0(k1_relat_1(B_43),A_44) = k1_relat_1(k7_relat_1(B_43,A_44))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_395,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,k1_relat_1(B_58)) = k1_relat_1(k7_relat_1(B_58,A_57))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_2])).

tff(c_767,plain,(
    ! [B_75,B_76] :
      ( k1_relat_1(k7_relat_1(B_75,k4_xboole_0(k1_relat_1(B_75),B_76))) = k4_xboole_0(k1_relat_1(B_75),B_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_395])).

tff(c_980,plain,(
    ! [C_79,B_80] :
      ( k1_relat_1(k4_xboole_0(C_79,k7_relat_1(C_79,B_80))) = k4_xboole_0(k1_relat_1(C_79),B_80)
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(C_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_767])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_665,plain,(
    ! [B_71,A_72] :
      ( k4_xboole_0(k1_relat_1(B_71),k1_relat_1(k7_relat_1(B_71,A_72))) = k4_xboole_0(k1_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_16])).

tff(c_26,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_26])).

tff(c_702,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_30])).

tff(c_728,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_702])).

tff(c_998,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_728])).

tff(c_1026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.45  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.70/1.45  
% 2.70/1.45  %Foreground sorts:
% 2.70/1.45  
% 2.70/1.45  
% 2.70/1.45  %Background operators:
% 2.70/1.45  
% 2.70/1.45  
% 2.70/1.45  %Foreground operators:
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.45  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.70/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.70/1.45  
% 2.70/1.46  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 2.70/1.46  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.46  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.70/1.46  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 2.70/1.46  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.70/1.46  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.70/1.46  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.70/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.70/1.46  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.70/1.46  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.46  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.46  tff(c_18, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.46  tff(c_22, plain, (![C_19, A_17, B_18]: (k7_relat_1(C_19, k6_subset_1(A_17, B_18))=k6_subset_1(C_19, k7_relat_1(C_19, B_18)) | ~r1_tarski(k1_relat_1(C_19), A_17) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.46  tff(c_361, plain, (![C_51, A_52, B_53]: (k7_relat_1(C_51, k4_xboole_0(A_52, B_53))=k4_xboole_0(C_51, k7_relat_1(C_51, B_53)) | ~r1_tarski(k1_relat_1(C_51), A_52) | ~v1_relat_1(C_51))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 2.70/1.46  tff(c_365, plain, (![C_51, B_53]: (k7_relat_1(C_51, k4_xboole_0(k1_relat_1(C_51), B_53))=k4_xboole_0(C_51, k7_relat_1(C_51, B_53)) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_8, c_361])).
% 2.70/1.46  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.46  tff(c_85, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.46  tff(c_92, plain, (![A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k4_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_14, c_85])).
% 2.70/1.46  tff(c_195, plain, (![B_43, A_44]: (k3_xboole_0(k1_relat_1(B_43), A_44)=k1_relat_1(k7_relat_1(B_43, A_44)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.70/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.46  tff(c_395, plain, (![A_57, B_58]: (k3_xboole_0(A_57, k1_relat_1(B_58))=k1_relat_1(k7_relat_1(B_58, A_57)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_195, c_2])).
% 2.70/1.46  tff(c_767, plain, (![B_75, B_76]: (k1_relat_1(k7_relat_1(B_75, k4_xboole_0(k1_relat_1(B_75), B_76)))=k4_xboole_0(k1_relat_1(B_75), B_76) | ~v1_relat_1(B_75))), inference(superposition, [status(thm), theory('equality')], [c_92, c_395])).
% 2.70/1.46  tff(c_980, plain, (![C_79, B_80]: (k1_relat_1(k4_xboole_0(C_79, k7_relat_1(C_79, B_80)))=k4_xboole_0(k1_relat_1(C_79), B_80) | ~v1_relat_1(C_79) | ~v1_relat_1(C_79))), inference(superposition, [status(thm), theory('equality')], [c_365, c_767])).
% 2.70/1.46  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.46  tff(c_665, plain, (![B_71, A_72]: (k4_xboole_0(k1_relat_1(B_71), k1_relat_1(k7_relat_1(B_71, A_72)))=k4_xboole_0(k1_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_195, c_16])).
% 2.70/1.46  tff(c_26, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.46  tff(c_30, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_26])).
% 2.70/1.46  tff(c_702, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_665, c_30])).
% 2.70/1.46  tff(c_728, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_702])).
% 2.70/1.46  tff(c_998, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_980, c_728])).
% 2.70/1.46  tff(c_1026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_998])).
% 2.70/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.46  
% 2.70/1.46  Inference rules
% 2.70/1.46  ----------------------
% 2.70/1.46  #Ref     : 0
% 2.70/1.46  #Sup     : 262
% 2.70/1.46  #Fact    : 0
% 2.70/1.46  #Define  : 0
% 2.70/1.46  #Split   : 0
% 2.70/1.46  #Chain   : 0
% 2.70/1.46  #Close   : 0
% 2.70/1.46  
% 2.70/1.46  Ordering : KBO
% 2.70/1.46  
% 2.70/1.46  Simplification rules
% 2.70/1.46  ----------------------
% 2.70/1.46  #Subsume      : 35
% 2.70/1.46  #Demod        : 115
% 2.70/1.46  #Tautology    : 126
% 2.70/1.46  #SimpNegUnit  : 0
% 2.70/1.46  #BackRed      : 0
% 2.70/1.46  
% 2.70/1.46  #Partial instantiations: 0
% 2.70/1.46  #Strategies tried      : 1
% 2.70/1.46  
% 2.70/1.46  Timing (in seconds)
% 2.70/1.46  ----------------------
% 2.70/1.46  Preprocessing        : 0.31
% 2.70/1.46  Parsing              : 0.16
% 2.70/1.46  CNF conversion       : 0.02
% 2.70/1.46  Main loop            : 0.39
% 2.70/1.46  Inferencing          : 0.15
% 2.70/1.46  Reduction            : 0.13
% 2.70/1.46  Demodulation         : 0.10
% 2.70/1.46  BG Simplification    : 0.02
% 2.70/1.46  Subsumption          : 0.06
% 2.70/1.46  Abstraction          : 0.03
% 2.70/1.46  MUC search           : 0.00
% 2.70/1.46  Cooper               : 0.00
% 2.70/1.46  Total                : 0.72
% 2.70/1.46  Index Insertion      : 0.00
% 2.70/1.46  Index Deletion       : 0.00
% 2.70/1.46  Index Matching       : 0.00
% 2.70/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
