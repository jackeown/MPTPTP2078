%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:43 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  69 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_45,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_136,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,k4_xboole_0(B_41,C_42))
      | ~ r1_xboole_0(A_40,C_42)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    ! [A_40] :
      ( ~ r1_xboole_0(A_40,k1_xboole_0)
      | ~ r1_xboole_0(A_40,'#skF_2')
      | r1_xboole_0(A_40,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_136])).

tff(c_159,plain,(
    ! [A_43] :
      ( ~ r1_xboole_0(A_43,'#skF_2')
      | r1_xboole_0(A_43,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_170,plain,(
    ! [A_6] : r1_xboole_0(k4_xboole_0(A_6,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_159])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [C_18,A_16,B_17] :
      ( k7_relat_1(C_18,k6_subset_1(A_16,B_17)) = k6_subset_1(C_18,k7_relat_1(C_18,B_17))
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_220,plain,(
    ! [C_50,A_51,B_52] :
      ( k7_relat_1(C_50,k4_xboole_0(A_51,B_52)) = k4_xboole_0(C_50,k7_relat_1(C_50,B_52))
      | ~ r1_tarski(k1_relat_1(C_50),A_51)
      | ~ v1_relat_1(C_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_234,plain,(
    ! [C_54,B_55] :
      ( k7_relat_1(C_54,k4_xboole_0(k1_relat_1(C_54),B_55)) = k4_xboole_0(C_54,k7_relat_1(C_54,B_55))
      | ~ v1_relat_1(C_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_220])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_610,plain,(
    ! [C_84,B_85,B_86] :
      ( k7_relat_1(k4_xboole_0(C_84,k7_relat_1(C_84,B_85)),B_86) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(C_84),B_85),B_86)
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_20])).

tff(c_863,plain,(
    ! [C_95] :
      ( k7_relat_1(k4_xboole_0(C_95,k7_relat_1(C_95,'#skF_2')),'#skF_1') = k1_xboole_0
      | ~ v1_relat_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_170,c_610])).

tff(c_24,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_896,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_863,c_29])).

tff(c_918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:51:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.43  
% 2.97/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.44  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.44  
% 2.97/1.44  %Foreground sorts:
% 2.97/1.44  
% 2.97/1.44  
% 2.97/1.44  %Background operators:
% 2.97/1.44  
% 2.97/1.44  
% 2.97/1.44  %Foreground operators:
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.97/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.44  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.97/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.44  
% 2.97/1.45  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 2.97/1.45  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.97/1.45  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.97/1.45  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.97/1.45  tff(f_47, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 2.97/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.97/1.45  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.97/1.45  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 2.97/1.45  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 2.97/1.45  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.45  tff(c_14, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.45  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.45  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.45  tff(c_45, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.45  tff(c_57, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.97/1.45  tff(c_136, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, k4_xboole_0(B_41, C_42)) | ~r1_xboole_0(A_40, C_42) | r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.45  tff(c_143, plain, (![A_40]: (~r1_xboole_0(A_40, k1_xboole_0) | ~r1_xboole_0(A_40, '#skF_2') | r1_xboole_0(A_40, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_136])).
% 2.97/1.45  tff(c_159, plain, (![A_43]: (~r1_xboole_0(A_43, '#skF_2') | r1_xboole_0(A_43, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_143])).
% 2.97/1.45  tff(c_170, plain, (![A_6]: (r1_xboole_0(k4_xboole_0(A_6, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_159])).
% 2.97/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.45  tff(c_18, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.45  tff(c_22, plain, (![C_18, A_16, B_17]: (k7_relat_1(C_18, k6_subset_1(A_16, B_17))=k6_subset_1(C_18, k7_relat_1(C_18, B_17)) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.97/1.45  tff(c_220, plain, (![C_50, A_51, B_52]: (k7_relat_1(C_50, k4_xboole_0(A_51, B_52))=k4_xboole_0(C_50, k7_relat_1(C_50, B_52)) | ~r1_tarski(k1_relat_1(C_50), A_51) | ~v1_relat_1(C_50))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 2.97/1.45  tff(c_234, plain, (![C_54, B_55]: (k7_relat_1(C_54, k4_xboole_0(k1_relat_1(C_54), B_55))=k4_xboole_0(C_54, k7_relat_1(C_54, B_55)) | ~v1_relat_1(C_54))), inference(resolution, [status(thm)], [c_6, c_220])).
% 2.97/1.45  tff(c_20, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.45  tff(c_610, plain, (![C_84, B_85, B_86]: (k7_relat_1(k4_xboole_0(C_84, k7_relat_1(C_84, B_85)), B_86)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(C_84), B_85), B_86) | ~v1_relat_1(C_84) | ~v1_relat_1(C_84))), inference(superposition, [status(thm), theory('equality')], [c_234, c_20])).
% 2.97/1.45  tff(c_863, plain, (![C_95]: (k7_relat_1(k4_xboole_0(C_95, k7_relat_1(C_95, '#skF_2')), '#skF_1')=k1_xboole_0 | ~v1_relat_1(C_95))), inference(resolution, [status(thm)], [c_170, c_610])).
% 2.97/1.45  tff(c_24, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.45  tff(c_29, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 2.97/1.45  tff(c_896, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_863, c_29])).
% 2.97/1.45  tff(c_918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_896])).
% 2.97/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.45  
% 2.97/1.45  Inference rules
% 2.97/1.45  ----------------------
% 2.97/1.45  #Ref     : 0
% 2.97/1.45  #Sup     : 220
% 2.97/1.45  #Fact    : 0
% 2.97/1.45  #Define  : 0
% 2.97/1.45  #Split   : 3
% 2.97/1.45  #Chain   : 0
% 2.97/1.45  #Close   : 0
% 2.97/1.45  
% 2.97/1.45  Ordering : KBO
% 2.97/1.45  
% 2.97/1.45  Simplification rules
% 2.97/1.45  ----------------------
% 2.97/1.45  #Subsume      : 39
% 2.97/1.45  #Demod        : 76
% 2.97/1.45  #Tautology    : 61
% 2.97/1.45  #SimpNegUnit  : 0
% 2.97/1.45  #BackRed      : 0
% 2.97/1.45  
% 2.97/1.45  #Partial instantiations: 0
% 2.97/1.45  #Strategies tried      : 1
% 2.97/1.45  
% 2.97/1.45  Timing (in seconds)
% 2.97/1.45  ----------------------
% 2.97/1.45  Preprocessing        : 0.29
% 2.97/1.45  Parsing              : 0.16
% 2.97/1.45  CNF conversion       : 0.02
% 2.97/1.45  Main loop            : 0.39
% 2.97/1.45  Inferencing          : 0.14
% 2.97/1.45  Reduction            : 0.12
% 2.97/1.45  Demodulation         : 0.09
% 2.97/1.45  BG Simplification    : 0.02
% 2.97/1.45  Subsumption          : 0.09
% 2.97/1.45  Abstraction          : 0.02
% 2.97/1.45  MUC search           : 0.00
% 2.97/1.45  Cooper               : 0.00
% 2.97/1.45  Total                : 0.71
% 2.97/1.45  Index Insertion      : 0.00
% 2.97/1.45  Index Deletion       : 0.00
% 2.97/1.45  Index Matching       : 0.00
% 2.97/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
