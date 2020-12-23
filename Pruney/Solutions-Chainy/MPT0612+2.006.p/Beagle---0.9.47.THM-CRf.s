%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:42 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  72 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_xboole_0(A_34,k4_xboole_0(C_35,B_36))
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_34,C_35,B_36] :
      ( k3_xboole_0(A_34,k4_xboole_0(C_35,B_36)) = k1_xboole_0
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [B_30,A_31] : k1_setfam_1(k2_tarski(B_30,A_31)) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_12,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k4_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k1_relat_1(k6_subset_1(B_15,k7_relat_1(B_15,A_14))) = k6_subset_1(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_353,plain,(
    ! [B_55,A_56] :
      ( k1_relat_1(k4_xboole_0(B_55,k7_relat_1(B_55,A_56))) = k4_xboole_0(k1_relat_1(B_55),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_178,plain,(
    ! [B_40,A_41] :
      ( k7_relat_1(B_40,A_41) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_40),A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_188,plain,(
    ! [B_40,B_2] :
      ( k7_relat_1(B_40,B_2) = k1_xboole_0
      | ~ v1_relat_1(B_40)
      | k3_xboole_0(k1_relat_1(B_40),B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_398,plain,(
    ! [B_68,A_69,B_70] :
      ( k7_relat_1(k4_xboole_0(B_68,k7_relat_1(B_68,A_69)),B_70) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_68,k7_relat_1(B_68,A_69)))
      | k3_xboole_0(k4_xboole_0(k1_relat_1(B_68),A_69),B_70) != k1_xboole_0
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_188])).

tff(c_403,plain,(
    ! [A_71,A_72,B_73] :
      ( k7_relat_1(k4_xboole_0(A_71,k7_relat_1(A_71,A_72)),B_73) = k1_xboole_0
      | k3_xboole_0(k4_xboole_0(k1_relat_1(A_71),A_72),B_73) != k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_14,c_398])).

tff(c_22,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_422,plain,
    ( k3_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'),'#skF_2'),'#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_28])).

tff(c_434,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_99,c_422])).

tff(c_438,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_434])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.23  
% 2.18/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.23  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.23  
% 2.18/1.23  %Foreground sorts:
% 2.18/1.23  
% 2.18/1.23  
% 2.18/1.23  %Background operators:
% 2.18/1.23  
% 2.18/1.23  
% 2.18/1.23  %Foreground operators:
% 2.18/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.23  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.18/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.23  
% 2.18/1.25  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 2.18/1.25  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.18/1.25  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.18/1.25  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.18/1.25  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.18/1.25  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.18/1.25  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.18/1.25  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.18/1.25  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.18/1.25  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.25  tff(c_150, plain, (![A_34, C_35, B_36]: (r1_xboole_0(A_34, k4_xboole_0(C_35, B_36)) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.25  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.25  tff(c_154, plain, (![A_34, C_35, B_36]: (k3_xboole_0(A_34, k4_xboole_0(C_35, B_36))=k1_xboole_0 | ~r1_tarski(A_34, B_36))), inference(resolution, [status(thm)], [c_150, c_2])).
% 2.18/1.25  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.25  tff(c_8, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.25  tff(c_72, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.25  tff(c_93, plain, (![B_30, A_31]: (k1_setfam_1(k2_tarski(B_30, A_31))=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 2.18/1.25  tff(c_12, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.25  tff(c_99, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 2.18/1.25  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k4_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.25  tff(c_10, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.25  tff(c_16, plain, (![B_15, A_14]: (k1_relat_1(k6_subset_1(B_15, k7_relat_1(B_15, A_14)))=k6_subset_1(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.25  tff(c_353, plain, (![B_55, A_56]: (k1_relat_1(k4_xboole_0(B_55, k7_relat_1(B_55, A_56)))=k4_xboole_0(k1_relat_1(B_55), A_56) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.18/1.25  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.25  tff(c_178, plain, (![B_40, A_41]: (k7_relat_1(B_40, A_41)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_40), A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.25  tff(c_188, plain, (![B_40, B_2]: (k7_relat_1(B_40, B_2)=k1_xboole_0 | ~v1_relat_1(B_40) | k3_xboole_0(k1_relat_1(B_40), B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_178])).
% 2.18/1.25  tff(c_398, plain, (![B_68, A_69, B_70]: (k7_relat_1(k4_xboole_0(B_68, k7_relat_1(B_68, A_69)), B_70)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_68, k7_relat_1(B_68, A_69))) | k3_xboole_0(k4_xboole_0(k1_relat_1(B_68), A_69), B_70)!=k1_xboole_0 | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_353, c_188])).
% 2.18/1.25  tff(c_403, plain, (![A_71, A_72, B_73]: (k7_relat_1(k4_xboole_0(A_71, k7_relat_1(A_71, A_72)), B_73)=k1_xboole_0 | k3_xboole_0(k4_xboole_0(k1_relat_1(A_71), A_72), B_73)!=k1_xboole_0 | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_14, c_398])).
% 2.18/1.25  tff(c_22, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.25  tff(c_28, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 2.18/1.25  tff(c_422, plain, (k3_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'), '#skF_2'), '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_403, c_28])).
% 2.18/1.25  tff(c_434, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_99, c_422])).
% 2.18/1.25  tff(c_438, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_434])).
% 2.18/1.25  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_438])).
% 2.18/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  Inference rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Ref     : 0
% 2.18/1.25  #Sup     : 100
% 2.18/1.25  #Fact    : 0
% 2.18/1.25  #Define  : 0
% 2.18/1.25  #Split   : 0
% 2.18/1.25  #Chain   : 0
% 2.18/1.25  #Close   : 0
% 2.18/1.25  
% 2.18/1.25  Ordering : KBO
% 2.18/1.25  
% 2.18/1.25  Simplification rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Subsume      : 23
% 2.18/1.25  #Demod        : 9
% 2.18/1.25  #Tautology    : 49
% 2.18/1.25  #SimpNegUnit  : 0
% 2.18/1.25  #BackRed      : 0
% 2.18/1.25  
% 2.18/1.25  #Partial instantiations: 0
% 2.18/1.25  #Strategies tried      : 1
% 2.18/1.25  
% 2.18/1.25  Timing (in seconds)
% 2.18/1.25  ----------------------
% 2.18/1.25  Preprocessing        : 0.28
% 2.18/1.25  Parsing              : 0.15
% 2.18/1.25  CNF conversion       : 0.02
% 2.18/1.25  Main loop            : 0.22
% 2.18/1.25  Inferencing          : 0.08
% 2.18/1.25  Reduction            : 0.07
% 2.18/1.25  Demodulation         : 0.05
% 2.18/1.25  BG Simplification    : 0.01
% 2.18/1.25  Subsumption          : 0.04
% 2.18/1.25  Abstraction          : 0.01
% 2.18/1.25  MUC search           : 0.00
% 2.18/1.25  Cooper               : 0.00
% 2.18/1.25  Total                : 0.53
% 2.18/1.25  Index Insertion      : 0.00
% 2.18/1.25  Index Deletion       : 0.00
% 2.18/1.25  Index Matching       : 0.00
% 2.18/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
