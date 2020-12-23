%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   46 (  54 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  57 expanded)
%              Number of equality atoms :   25 (  33 expanded)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_326,plain,(
    ! [C_51,A_52,B_53] :
      ( k7_relat_1(C_51,k4_xboole_0(A_52,B_53)) = k4_xboole_0(C_51,k7_relat_1(C_51,B_53))
      | ~ r1_tarski(k1_relat_1(C_51),A_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_330,plain,(
    ! [C_51,B_53] :
      ( k7_relat_1(C_51,k4_xboole_0(k1_relat_1(C_51),B_53)) = k4_xboole_0(C_51,k7_relat_1(C_51,B_53))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_326])).

tff(c_14,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(B_33,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_74])).

tff(c_18,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,(
    ! [B_33,A_32] : k3_xboole_0(B_33,A_32) = k3_xboole_0(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_18])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_235,plain,(
    ! [A_43,B_44] : k3_xboole_0(k4_xboole_0(A_43,B_44),A_43) = k4_xboole_0(A_43,B_44) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_299,plain,(
    ! [B_47,B_48] : k3_xboole_0(B_47,k4_xboole_0(B_47,B_48)) = k4_xboole_0(B_47,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_235])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k3_xboole_0(k1_relat_1(B_19),A_18) = k1_relat_1(k7_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_544,plain,(
    ! [B_69,B_70] :
      ( k1_relat_1(k7_relat_1(B_69,k4_xboole_0(k1_relat_1(B_69),B_70))) = k4_xboole_0(k1_relat_1(B_69),B_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_22])).

tff(c_735,plain,(
    ! [C_75,B_76] :
      ( k1_relat_1(k4_xboole_0(C_75,k7_relat_1(C_75,B_76))) = k4_xboole_0(k1_relat_1(C_75),B_76)
      | ~ v1_relat_1(C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_544])).

tff(c_24,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_24])).

tff(c_773,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_28])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.42  
% 2.50/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.42  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.50/1.42  
% 2.50/1.42  %Foreground sorts:
% 2.50/1.42  
% 2.50/1.42  
% 2.50/1.42  %Background operators:
% 2.50/1.42  
% 2.50/1.42  
% 2.50/1.42  %Foreground operators:
% 2.50/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.50/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.50/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.50/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.42  
% 2.50/1.43  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.50/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.43  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.50/1.43  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 2.50/1.43  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.50/1.43  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.50/1.43  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.50/1.43  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.50/1.43  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.50/1.43  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.50/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.43  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.43  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.50/1.43  tff(c_326, plain, (![C_51, A_52, B_53]: (k7_relat_1(C_51, k4_xboole_0(A_52, B_53))=k4_xboole_0(C_51, k7_relat_1(C_51, B_53)) | ~r1_tarski(k1_relat_1(C_51), A_52) | ~v1_relat_1(C_51))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 2.50/1.43  tff(c_330, plain, (![C_51, B_53]: (k7_relat_1(C_51, k4_xboole_0(k1_relat_1(C_51), B_53))=k4_xboole_0(C_51, k7_relat_1(C_51, B_53)) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_6, c_326])).
% 2.50/1.43  tff(c_14, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.43  tff(c_74, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.43  tff(c_107, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(B_33, A_32))), inference(superposition, [status(thm), theory('equality')], [c_14, c_74])).
% 2.50/1.43  tff(c_18, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.43  tff(c_113, plain, (![B_33, A_32]: (k3_xboole_0(B_33, A_32)=k3_xboole_0(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_107, c_18])).
% 2.50/1.43  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.43  tff(c_89, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.50/1.43  tff(c_235, plain, (![A_43, B_44]: (k3_xboole_0(k4_xboole_0(A_43, B_44), A_43)=k4_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_12, c_89])).
% 2.50/1.43  tff(c_299, plain, (![B_47, B_48]: (k3_xboole_0(B_47, k4_xboole_0(B_47, B_48))=k4_xboole_0(B_47, B_48))), inference(superposition, [status(thm), theory('equality')], [c_113, c_235])).
% 2.50/1.43  tff(c_22, plain, (![B_19, A_18]: (k3_xboole_0(k1_relat_1(B_19), A_18)=k1_relat_1(k7_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.50/1.43  tff(c_544, plain, (![B_69, B_70]: (k1_relat_1(k7_relat_1(B_69, k4_xboole_0(k1_relat_1(B_69), B_70)))=k4_xboole_0(k1_relat_1(B_69), B_70) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_299, c_22])).
% 2.50/1.43  tff(c_735, plain, (![C_75, B_76]: (k1_relat_1(k4_xboole_0(C_75, k7_relat_1(C_75, B_76)))=k4_xboole_0(k1_relat_1(C_75), B_76) | ~v1_relat_1(C_75) | ~v1_relat_1(C_75))), inference(superposition, [status(thm), theory('equality')], [c_330, c_544])).
% 2.50/1.43  tff(c_24, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.50/1.43  tff(c_28, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_24])).
% 2.50/1.43  tff(c_773, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_735, c_28])).
% 2.50/1.43  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_773])).
% 2.50/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.43  
% 2.50/1.43  Inference rules
% 2.50/1.43  ----------------------
% 2.50/1.43  #Ref     : 0
% 2.50/1.43  #Sup     : 201
% 2.50/1.43  #Fact    : 0
% 2.50/1.43  #Define  : 0
% 2.50/1.43  #Split   : 0
% 2.50/1.43  #Chain   : 0
% 2.50/1.43  #Close   : 0
% 2.50/1.43  
% 2.50/1.43  Ordering : KBO
% 2.50/1.43  
% 2.50/1.43  Simplification rules
% 2.50/1.43  ----------------------
% 2.50/1.43  #Subsume      : 22
% 2.50/1.43  #Demod        : 54
% 2.50/1.43  #Tautology    : 99
% 2.50/1.43  #SimpNegUnit  : 0
% 2.50/1.43  #BackRed      : 0
% 2.50/1.43  
% 2.50/1.43  #Partial instantiations: 0
% 2.50/1.43  #Strategies tried      : 1
% 2.50/1.43  
% 2.50/1.43  Timing (in seconds)
% 2.50/1.43  ----------------------
% 2.50/1.44  Preprocessing        : 0.31
% 2.50/1.44  Parsing              : 0.17
% 2.50/1.44  CNF conversion       : 0.02
% 2.50/1.44  Main loop            : 0.32
% 2.50/1.44  Inferencing          : 0.13
% 2.50/1.44  Reduction            : 0.10
% 2.50/1.44  Demodulation         : 0.08
% 2.50/1.44  BG Simplification    : 0.02
% 2.50/1.44  Subsumption          : 0.05
% 2.50/1.44  Abstraction          : 0.02
% 2.50/1.44  MUC search           : 0.00
% 2.50/1.44  Cooper               : 0.00
% 2.50/1.44  Total                : 0.66
% 2.50/1.44  Index Insertion      : 0.00
% 2.50/1.44  Index Deletion       : 0.00
% 2.50/1.44  Index Matching       : 0.00
% 2.50/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
