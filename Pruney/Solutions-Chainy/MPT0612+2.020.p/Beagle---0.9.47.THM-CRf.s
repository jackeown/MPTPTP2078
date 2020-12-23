%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:44 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  73 expanded)
%              Number of equality atoms :   17 (  24 expanded)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_xboole_0(A_23,k4_xboole_0(C_24,B_25))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_28,C_29,B_30] :
      ( k4_xboole_0(A_28,k4_xboole_0(C_29,B_30)) = A_28
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(resolution,[status(thm)],[c_44,c_8])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_34,A_35,C_36,B_37] :
      ( r1_xboole_0(A_34,A_35)
      | ~ r1_tarski(A_34,k4_xboole_0(C_36,B_37))
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_99,plain,(
    ! [C_36,B_37,A_35] :
      ( r1_xboole_0(k4_xboole_0(C_36,B_37),A_35)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_14,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(C_15,k6_subset_1(A_13,B_14)) = k6_subset_1(C_15,k7_relat_1(C_15,B_14))
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_108,plain,(
    ! [C_41,A_42,B_43] :
      ( k7_relat_1(C_41,k4_xboole_0(A_42,B_43)) = k4_xboole_0(C_41,k7_relat_1(C_41,B_43))
      | ~ r1_tarski(k1_relat_1(C_41),A_42)
      | ~ v1_relat_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_261,plain,(
    ! [C_71,B_72] :
      ( k7_relat_1(C_71,k4_xboole_0(k1_relat_1(C_71),B_72)) = k4_xboole_0(C_71,k7_relat_1(C_71,B_72))
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_16,plain,(
    ! [C_12,A_10,B_11] :
      ( k7_relat_1(k7_relat_1(C_12,A_10),B_11) = k1_xboole_0
      | ~ r1_xboole_0(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_892,plain,(
    ! [C_179,B_180,B_181] :
      ( k7_relat_1(k4_xboole_0(C_179,k7_relat_1(C_179,B_180)),B_181) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(C_179),B_180),B_181)
      | ~ v1_relat_1(C_179)
      | ~ v1_relat_1(C_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_16])).

tff(c_926,plain,(
    ! [C_182,B_183,A_184] :
      ( k7_relat_1(k4_xboole_0(C_182,k7_relat_1(C_182,B_183)),A_184) = k1_xboole_0
      | ~ v1_relat_1(C_182)
      | ~ r1_tarski(A_184,B_183) ) ),
    inference(resolution,[status(thm)],[c_99,c_892])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_25,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_956,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_25])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.48  
% 3.28/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.48  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.28/1.48  
% 3.28/1.48  %Foreground sorts:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Background operators:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Foreground operators:
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.48  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.28/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.48  
% 3.28/1.49  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 3.28/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.49  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.28/1.49  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.28/1.49  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.28/1.49  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 3.28/1.49  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 3.28/1.49  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.49  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.49  tff(c_44, plain, (![A_23, C_24, B_25]: (r1_xboole_0(A_23, k4_xboole_0(C_24, B_25)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.49  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.49  tff(c_60, plain, (![A_28, C_29, B_30]: (k4_xboole_0(A_28, k4_xboole_0(C_29, B_30))=A_28 | ~r1_tarski(A_28, B_30))), inference(resolution, [status(thm)], [c_44, c_8])).
% 3.28/1.49  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.49  tff(c_93, plain, (![A_34, A_35, C_36, B_37]: (r1_xboole_0(A_34, A_35) | ~r1_tarski(A_34, k4_xboole_0(C_36, B_37)) | ~r1_tarski(A_35, B_37))), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 3.28/1.49  tff(c_99, plain, (![C_36, B_37, A_35]: (r1_xboole_0(k4_xboole_0(C_36, B_37), A_35) | ~r1_tarski(A_35, B_37))), inference(resolution, [status(thm)], [c_6, c_93])).
% 3.28/1.49  tff(c_14, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.49  tff(c_18, plain, (![C_15, A_13, B_14]: (k7_relat_1(C_15, k6_subset_1(A_13, B_14))=k6_subset_1(C_15, k7_relat_1(C_15, B_14)) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.49  tff(c_108, plain, (![C_41, A_42, B_43]: (k7_relat_1(C_41, k4_xboole_0(A_42, B_43))=k4_xboole_0(C_41, k7_relat_1(C_41, B_43)) | ~r1_tarski(k1_relat_1(C_41), A_42) | ~v1_relat_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 3.28/1.49  tff(c_261, plain, (![C_71, B_72]: (k7_relat_1(C_71, k4_xboole_0(k1_relat_1(C_71), B_72))=k4_xboole_0(C_71, k7_relat_1(C_71, B_72)) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_6, c_108])).
% 3.28/1.49  tff(c_16, plain, (![C_12, A_10, B_11]: (k7_relat_1(k7_relat_1(C_12, A_10), B_11)=k1_xboole_0 | ~r1_xboole_0(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.49  tff(c_892, plain, (![C_179, B_180, B_181]: (k7_relat_1(k4_xboole_0(C_179, k7_relat_1(C_179, B_180)), B_181)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(C_179), B_180), B_181) | ~v1_relat_1(C_179) | ~v1_relat_1(C_179))), inference(superposition, [status(thm), theory('equality')], [c_261, c_16])).
% 3.28/1.49  tff(c_926, plain, (![C_182, B_183, A_184]: (k7_relat_1(k4_xboole_0(C_182, k7_relat_1(C_182, B_183)), A_184)=k1_xboole_0 | ~v1_relat_1(C_182) | ~r1_tarski(A_184, B_183))), inference(resolution, [status(thm)], [c_99, c_892])).
% 3.28/1.49  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.49  tff(c_25, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 3.28/1.49  tff(c_956, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_926, c_25])).
% 3.28/1.49  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_956])).
% 3.28/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.49  
% 3.28/1.49  Inference rules
% 3.28/1.49  ----------------------
% 3.28/1.49  #Ref     : 0
% 3.28/1.49  #Sup     : 297
% 3.28/1.49  #Fact    : 0
% 3.28/1.49  #Define  : 0
% 3.28/1.49  #Split   : 5
% 3.28/1.49  #Chain   : 0
% 3.28/1.49  #Close   : 0
% 3.28/1.49  
% 3.28/1.49  Ordering : KBO
% 3.28/1.49  
% 3.28/1.49  Simplification rules
% 3.28/1.49  ----------------------
% 3.28/1.49  #Subsume      : 90
% 3.28/1.49  #Demod        : 9
% 3.28/1.49  #Tautology    : 34
% 3.28/1.49  #SimpNegUnit  : 0
% 3.28/1.49  #BackRed      : 0
% 3.28/1.49  
% 3.28/1.49  #Partial instantiations: 0
% 3.28/1.49  #Strategies tried      : 1
% 3.28/1.49  
% 3.28/1.49  Timing (in seconds)
% 3.28/1.49  ----------------------
% 3.28/1.49  Preprocessing        : 0.29
% 3.28/1.49  Parsing              : 0.16
% 3.28/1.49  CNF conversion       : 0.02
% 3.28/1.49  Main loop            : 0.44
% 3.28/1.49  Inferencing          : 0.15
% 3.28/1.49  Reduction            : 0.10
% 3.28/1.49  Demodulation         : 0.07
% 3.28/1.49  BG Simplification    : 0.02
% 3.28/1.49  Subsumption          : 0.14
% 3.28/1.49  Abstraction          : 0.02
% 3.28/1.49  MUC search           : 0.00
% 3.28/1.49  Cooper               : 0.00
% 3.28/1.49  Total                : 0.75
% 3.28/1.49  Index Insertion      : 0.00
% 3.28/1.49  Index Deletion       : 0.00
% 3.28/1.49  Index Matching       : 0.00
% 3.28/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
