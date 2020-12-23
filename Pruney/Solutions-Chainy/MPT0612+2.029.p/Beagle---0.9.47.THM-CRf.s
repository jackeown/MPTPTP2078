%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:45 EST 2020

% Result     : Theorem 33.31s
% Output     : CNFRefutation 33.31s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  69 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_41,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k4_xboole_0(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_xboole_0(A_34,C_35)
      | ~ r1_tarski(A_34,k4_xboole_0(B_36,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [B_36,C_35,B_9] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_36,C_35),B_9),C_35) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_135,plain,(
    ! [B_52,C_53,B_54] : r1_xboole_0(k4_xboole_0(B_52,k2_xboole_0(C_53,B_54)),C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_68])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [C_53,B_52,B_54] : r1_xboole_0(C_53,k4_xboole_0(B_52,k2_xboole_0(C_53,B_54))) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_14,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k6_subset_1(B_21,k7_relat_1(B_21,A_20))) = k6_subset_1(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_359,plain,(
    ! [B_87,A_88] :
      ( k1_relat_1(k4_xboole_0(B_87,k7_relat_1(B_87,A_88))) = k4_xboole_0(k1_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_18,plain,(
    ! [A_17,B_19] :
      ( k7_relat_1(A_17,B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,k1_relat_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1858,plain,(
    ! [B_234,A_235,B_236] :
      ( k7_relat_1(k4_xboole_0(B_234,k7_relat_1(B_234,A_235)),B_236) = k1_xboole_0
      | ~ r1_xboole_0(B_236,k4_xboole_0(k1_relat_1(B_234),A_235))
      | ~ v1_relat_1(k4_xboole_0(B_234,k7_relat_1(B_234,A_235)))
      | ~ v1_relat_1(B_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_18])).

tff(c_91714,plain,(
    ! [B_2423,C_2424,B_2425] :
      ( k7_relat_1(k4_xboole_0(B_2423,k7_relat_1(B_2423,k2_xboole_0(C_2424,B_2425))),C_2424) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_2423,k7_relat_1(B_2423,k2_xboole_0(C_2424,B_2425))))
      | ~ v1_relat_1(B_2423) ) ),
    inference(resolution,[status(thm)],[c_148,c_1858])).

tff(c_91769,plain,(
    ! [A_2426,C_2427,B_2428] :
      ( k7_relat_1(k4_xboole_0(A_2426,k7_relat_1(A_2426,k2_xboole_0(C_2427,B_2428))),C_2427) = k1_xboole_0
      | ~ v1_relat_1(A_2426) ) ),
    inference(resolution,[status(thm)],[c_16,c_91714])).

tff(c_91881,plain,(
    ! [A_2429] :
      ( k7_relat_1(k4_xboole_0(A_2429,k7_relat_1(A_2429,'#skF_2')),'#skF_1') = k1_xboole_0
      | ~ v1_relat_1(A_2429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_91769])).

tff(c_22,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_91911,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91881,c_28])).

tff(c_91932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_91911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.31/24.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.31/24.89  
% 33.31/24.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.31/24.89  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 33.31/24.89  
% 33.31/24.89  %Foreground sorts:
% 33.31/24.89  
% 33.31/24.89  
% 33.31/24.89  %Background operators:
% 33.31/24.89  
% 33.31/24.89  
% 33.31/24.89  %Foreground operators:
% 33.31/24.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.31/24.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 33.31/24.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 33.31/24.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 33.31/24.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.31/24.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 33.31/24.89  tff('#skF_2', type, '#skF_2': $i).
% 33.31/24.89  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 33.31/24.89  tff('#skF_3', type, '#skF_3': $i).
% 33.31/24.89  tff('#skF_1', type, '#skF_1': $i).
% 33.31/24.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.31/24.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 33.31/24.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.31/24.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 33.31/24.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 33.31/24.89  
% 33.31/24.90  tff(f_67, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 33.31/24.90  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 33.31/24.90  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 33.31/24.90  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 33.31/24.90  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 33.31/24.90  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 33.31/24.90  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 33.31/24.90  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 33.31/24.90  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 33.31/24.90  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 33.31/24.90  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 33.31/24.90  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 33.31/24.90  tff(c_41, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 33.31/24.90  tff(c_49, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_41])).
% 33.31/24.90  tff(c_16, plain, (![A_15, B_16]: (v1_relat_1(k4_xboole_0(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 33.31/24.90  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 33.31/24.90  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 33.31/24.90  tff(c_63, plain, (![A_34, C_35, B_36]: (r1_xboole_0(A_34, C_35) | ~r1_tarski(A_34, k4_xboole_0(B_36, C_35)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 33.31/24.90  tff(c_68, plain, (![B_36, C_35, B_9]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_36, C_35), B_9), C_35))), inference(resolution, [status(thm)], [c_10, c_63])).
% 33.31/24.90  tff(c_135, plain, (![B_52, C_53, B_54]: (r1_xboole_0(k4_xboole_0(B_52, k2_xboole_0(C_53, B_54)), C_53))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_68])).
% 33.31/24.90  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 33.31/24.90  tff(c_148, plain, (![C_53, B_52, B_54]: (r1_xboole_0(C_53, k4_xboole_0(B_52, k2_xboole_0(C_53, B_54))))), inference(resolution, [status(thm)], [c_135, c_2])).
% 33.31/24.90  tff(c_14, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 33.31/24.90  tff(c_20, plain, (![B_21, A_20]: (k1_relat_1(k6_subset_1(B_21, k7_relat_1(B_21, A_20)))=k6_subset_1(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 33.31/24.90  tff(c_359, plain, (![B_87, A_88]: (k1_relat_1(k4_xboole_0(B_87, k7_relat_1(B_87, A_88)))=k4_xboole_0(k1_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 33.31/24.90  tff(c_18, plain, (![A_17, B_19]: (k7_relat_1(A_17, B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, k1_relat_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 33.31/24.90  tff(c_1858, plain, (![B_234, A_235, B_236]: (k7_relat_1(k4_xboole_0(B_234, k7_relat_1(B_234, A_235)), B_236)=k1_xboole_0 | ~r1_xboole_0(B_236, k4_xboole_0(k1_relat_1(B_234), A_235)) | ~v1_relat_1(k4_xboole_0(B_234, k7_relat_1(B_234, A_235))) | ~v1_relat_1(B_234))), inference(superposition, [status(thm), theory('equality')], [c_359, c_18])).
% 33.31/24.90  tff(c_91714, plain, (![B_2423, C_2424, B_2425]: (k7_relat_1(k4_xboole_0(B_2423, k7_relat_1(B_2423, k2_xboole_0(C_2424, B_2425))), C_2424)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_2423, k7_relat_1(B_2423, k2_xboole_0(C_2424, B_2425)))) | ~v1_relat_1(B_2423))), inference(resolution, [status(thm)], [c_148, c_1858])).
% 33.31/24.90  tff(c_91769, plain, (![A_2426, C_2427, B_2428]: (k7_relat_1(k4_xboole_0(A_2426, k7_relat_1(A_2426, k2_xboole_0(C_2427, B_2428))), C_2427)=k1_xboole_0 | ~v1_relat_1(A_2426))), inference(resolution, [status(thm)], [c_16, c_91714])).
% 33.31/24.90  tff(c_91881, plain, (![A_2429]: (k7_relat_1(k4_xboole_0(A_2429, k7_relat_1(A_2429, '#skF_2')), '#skF_1')=k1_xboole_0 | ~v1_relat_1(A_2429))), inference(superposition, [status(thm), theory('equality')], [c_49, c_91769])).
% 33.31/24.90  tff(c_22, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 33.31/24.90  tff(c_28, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 33.31/24.90  tff(c_91911, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91881, c_28])).
% 33.31/24.90  tff(c_91932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_91911])).
% 33.31/24.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.31/24.90  
% 33.31/24.90  Inference rules
% 33.31/24.90  ----------------------
% 33.31/24.90  #Ref     : 0
% 33.31/24.90  #Sup     : 21130
% 33.31/24.90  #Fact    : 0
% 33.31/24.90  #Define  : 0
% 33.31/24.90  #Split   : 0
% 33.31/24.90  #Chain   : 0
% 33.31/24.90  #Close   : 0
% 33.31/24.90  
% 33.31/24.90  Ordering : KBO
% 33.31/24.90  
% 33.31/24.90  Simplification rules
% 33.31/24.90  ----------------------
% 33.31/24.90  #Subsume      : 1338
% 33.31/24.90  #Demod        : 19302
% 33.31/24.90  #Tautology    : 12664
% 33.31/24.90  #SimpNegUnit  : 0
% 33.31/24.90  #BackRed      : 24
% 33.31/24.90  
% 33.31/24.90  #Partial instantiations: 0
% 33.31/24.90  #Strategies tried      : 1
% 33.31/24.90  
% 33.31/24.90  Timing (in seconds)
% 33.31/24.90  ----------------------
% 33.31/24.91  Preprocessing        : 0.29
% 33.31/24.91  Parsing              : 0.16
% 33.31/24.91  CNF conversion       : 0.02
% 33.31/24.91  Main loop            : 23.84
% 33.31/24.91  Inferencing          : 2.24
% 33.31/24.91  Reduction            : 15.10
% 33.31/24.91  Demodulation         : 13.99
% 33.31/24.91  BG Simplification    : 0.19
% 33.31/24.91  Subsumption          : 5.71
% 33.31/24.91  Abstraction          : 0.29
% 33.31/24.91  MUC search           : 0.00
% 33.31/24.91  Cooper               : 0.00
% 33.31/24.91  Total                : 24.16
% 33.31/24.91  Index Insertion      : 0.00
% 33.31/24.91  Index Deletion       : 0.00
% 33.31/24.91  Index Matching       : 0.00
% 33.31/24.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
