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
% DateTime   : Thu Dec  3 10:02:45 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  67 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_xboole_0(k4_xboole_0(A_4,B_5),B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_40])).

tff(c_71,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,k4_xboole_0(B_35,C_36))
      | ~ r1_xboole_0(A_34,C_36)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [A_34] :
      ( ~ r1_xboole_0(A_34,k1_xboole_0)
      | ~ r1_xboole_0(A_34,'#skF_2')
      | r1_xboole_0(A_34,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_71])).

tff(c_87,plain,(
    ! [A_37] :
      ( ~ r1_xboole_0(A_37,'#skF_2')
      | r1_xboole_0(A_37,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_96,plain,(
    ! [A_4] : r1_xboole_0(k4_xboole_0(A_4,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [C_18,A_16,B_17] :
      ( k7_relat_1(C_18,k6_subset_1(A_16,B_17)) = k6_subset_1(C_18,k7_relat_1(C_18,B_17))
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_199,plain,(
    ! [C_58,A_59,B_60] :
      ( k7_relat_1(C_58,k4_xboole_0(A_59,B_60)) = k4_xboole_0(C_58,k7_relat_1(C_58,B_60))
      | ~ r1_tarski(k1_relat_1(C_58),A_59)
      | ~ v1_relat_1(C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_313,plain,(
    ! [C_92,B_93,B_94] :
      ( k7_relat_1(C_92,k4_xboole_0(k2_xboole_0(k1_relat_1(C_92),B_93),B_94)) = k4_xboole_0(C_92,k7_relat_1(C_92,B_94))
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_10,c_199])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_787,plain,(
    ! [C_165,B_166,B_167,B_168] :
      ( k7_relat_1(k4_xboole_0(C_165,k7_relat_1(C_165,B_166)),B_167) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_165),B_168),B_166),B_167)
      | ~ v1_relat_1(C_165)
      | ~ v1_relat_1(C_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_16])).

tff(c_1062,plain,(
    ! [C_173] :
      ( k7_relat_1(k4_xboole_0(C_173,k7_relat_1(C_173,'#skF_2')),'#skF_1') = k1_xboole_0
      | ~ v1_relat_1(C_173) ) ),
    inference(resolution,[status(thm)],[c_96,c_787])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_1092,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_25])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  
% 3.16/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.16/1.54  
% 3.16/1.54  %Foreground sorts:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Background operators:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Foreground operators:
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.16/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.54  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.16/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.54  
% 3.16/1.56  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 3.16/1.56  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.16/1.56  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.16/1.56  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.16/1.56  tff(f_43, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 3.16/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.16/1.56  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.16/1.56  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 3.16/1.56  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 3.16/1.56  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.56  tff(c_8, plain, (![A_4, B_5]: (r1_xboole_0(k4_xboole_0(A_4, B_5), B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.56  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.56  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.56  tff(c_40, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.56  tff(c_52, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_40])).
% 3.16/1.56  tff(c_71, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, k4_xboole_0(B_35, C_36)) | ~r1_xboole_0(A_34, C_36) | r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.56  tff(c_77, plain, (![A_34]: (~r1_xboole_0(A_34, k1_xboole_0) | ~r1_xboole_0(A_34, '#skF_2') | r1_xboole_0(A_34, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_71])).
% 3.16/1.56  tff(c_87, plain, (![A_37]: (~r1_xboole_0(A_37, '#skF_2') | r1_xboole_0(A_37, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_77])).
% 3.16/1.56  tff(c_96, plain, (![A_4]: (r1_xboole_0(k4_xboole_0(A_4, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_87])).
% 3.16/1.56  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.56  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.56  tff(c_18, plain, (![C_18, A_16, B_17]: (k7_relat_1(C_18, k6_subset_1(A_16, B_17))=k6_subset_1(C_18, k7_relat_1(C_18, B_17)) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.56  tff(c_199, plain, (![C_58, A_59, B_60]: (k7_relat_1(C_58, k4_xboole_0(A_59, B_60))=k4_xboole_0(C_58, k7_relat_1(C_58, B_60)) | ~r1_tarski(k1_relat_1(C_58), A_59) | ~v1_relat_1(C_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 3.16/1.56  tff(c_313, plain, (![C_92, B_93, B_94]: (k7_relat_1(C_92, k4_xboole_0(k2_xboole_0(k1_relat_1(C_92), B_93), B_94))=k4_xboole_0(C_92, k7_relat_1(C_92, B_94)) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_10, c_199])).
% 3.16/1.56  tff(c_16, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.56  tff(c_787, plain, (![C_165, B_166, B_167, B_168]: (k7_relat_1(k4_xboole_0(C_165, k7_relat_1(C_165, B_166)), B_167)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_165), B_168), B_166), B_167) | ~v1_relat_1(C_165) | ~v1_relat_1(C_165))), inference(superposition, [status(thm), theory('equality')], [c_313, c_16])).
% 3.16/1.56  tff(c_1062, plain, (![C_173]: (k7_relat_1(k4_xboole_0(C_173, k7_relat_1(C_173, '#skF_2')), '#skF_1')=k1_xboole_0 | ~v1_relat_1(C_173))), inference(resolution, [status(thm)], [c_96, c_787])).
% 3.16/1.56  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.56  tff(c_25, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 3.16/1.56  tff(c_1092, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_25])).
% 3.16/1.56  tff(c_1113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1092])).
% 3.16/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.56  
% 3.16/1.56  Inference rules
% 3.16/1.56  ----------------------
% 3.16/1.56  #Ref     : 0
% 3.16/1.56  #Sup     : 268
% 3.16/1.56  #Fact    : 0
% 3.16/1.56  #Define  : 0
% 3.16/1.56  #Split   : 1
% 3.16/1.56  #Chain   : 0
% 3.16/1.56  #Close   : 0
% 3.16/1.56  
% 3.16/1.56  Ordering : KBO
% 3.16/1.56  
% 3.16/1.56  Simplification rules
% 3.16/1.56  ----------------------
% 3.16/1.56  #Subsume      : 35
% 3.16/1.56  #Demod        : 64
% 3.16/1.56  #Tautology    : 66
% 3.16/1.56  #SimpNegUnit  : 0
% 3.16/1.56  #BackRed      : 0
% 3.16/1.56  
% 3.16/1.56  #Partial instantiations: 0
% 3.16/1.56  #Strategies tried      : 1
% 3.16/1.56  
% 3.16/1.56  Timing (in seconds)
% 3.16/1.56  ----------------------
% 3.16/1.56  Preprocessing        : 0.29
% 3.16/1.56  Parsing              : 0.16
% 3.16/1.56  CNF conversion       : 0.02
% 3.16/1.56  Main loop            : 0.44
% 3.16/1.56  Inferencing          : 0.17
% 3.16/1.56  Reduction            : 0.14
% 3.16/1.56  Demodulation         : 0.11
% 3.16/1.56  BG Simplification    : 0.02
% 3.16/1.56  Subsumption          : 0.08
% 3.16/1.56  Abstraction          : 0.02
% 3.16/1.56  MUC search           : 0.00
% 3.16/1.56  Cooper               : 0.00
% 3.16/1.56  Total                : 0.75
% 3.16/1.56  Index Insertion      : 0.00
% 3.16/1.56  Index Deletion       : 0.00
% 3.16/1.56  Index Matching       : 0.00
% 3.16/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
