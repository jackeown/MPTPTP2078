%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  75 expanded)
%              Number of equality atoms :   18 (  26 expanded)
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_37,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_34])).

tff(c_54,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,k4_xboole_0(C_28,B_29))
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = A_4
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    ! [A_41,C_42,B_43] :
      ( k4_xboole_0(A_41,k4_xboole_0(C_42,B_43)) = A_41
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(resolution,[status(thm)],[c_54,c_6])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,k4_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    ! [A_44,A_45,C_46,B_47] :
      ( r1_xboole_0(A_44,A_45)
      | ~ r1_tarski(A_44,k4_xboole_0(C_46,B_47))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_10])).

tff(c_187,plain,(
    ! [C_46,B_47,A_45] :
      ( r1_xboole_0(k4_xboole_0(C_46,B_47),A_45)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(resolution,[status(thm)],[c_37,c_174])).

tff(c_12,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(C_16,k6_subset_1(A_14,B_15)) = k6_subset_1(C_16,k7_relat_1(C_16,B_15))
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_221,plain,(
    ! [C_54,A_55,B_56] :
      ( k7_relat_1(C_54,k4_xboole_0(A_55,B_56)) = k4_xboole_0(C_54,k7_relat_1(C_54,B_56))
      | ~ r1_tarski(k1_relat_1(C_54),A_55)
      | ~ v1_relat_1(C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16])).

tff(c_1690,plain,(
    ! [C_168,B_169] :
      ( k7_relat_1(C_168,k4_xboole_0(k1_relat_1(C_168),B_169)) = k4_xboole_0(C_168,k7_relat_1(C_168,B_169))
      | ~ v1_relat_1(C_168) ) ),
    inference(resolution,[status(thm)],[c_37,c_221])).

tff(c_14,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_13,A_11),B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5788,plain,(
    ! [C_351,B_352,B_353] :
      ( k7_relat_1(k4_xboole_0(C_351,k7_relat_1(C_351,B_352)),B_353) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(C_351),B_352),B_353)
      | ~ v1_relat_1(C_351)
      | ~ v1_relat_1(C_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1690,c_14])).

tff(c_6197,plain,(
    ! [C_369,B_370,A_371] :
      ( k7_relat_1(k4_xboole_0(C_369,k7_relat_1(C_369,B_370)),A_371) = k1_xboole_0
      | ~ v1_relat_1(C_369)
      | ~ r1_tarski(A_371,B_370) ) ),
    inference(resolution,[status(thm)],[c_187,c_5788])).

tff(c_18,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_6257,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6197,c_23])).

tff(c_6324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_6257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.97/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.20  
% 5.97/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.20  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.97/2.20  
% 5.97/2.20  %Foreground sorts:
% 5.97/2.20  
% 5.97/2.20  
% 5.97/2.20  %Background operators:
% 5.97/2.20  
% 5.97/2.20  
% 5.97/2.20  %Foreground operators:
% 5.97/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.97/2.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.97/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.97/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.97/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.97/2.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.97/2.20  tff('#skF_3', type, '#skF_3': $i).
% 5.97/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.97/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.97/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.97/2.20  
% 5.97/2.21  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 5.97/2.21  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.97/2.21  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.97/2.21  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.97/2.21  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.97/2.21  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.97/2.21  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 5.97/2.21  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 5.97/2.21  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.97/2.21  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.97/2.21  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.97/2.21  tff(c_34, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.97/2.21  tff(c_37, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_34])).
% 5.97/2.21  tff(c_54, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, k4_xboole_0(C_28, B_29)) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.97/2.21  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=A_4 | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.97/2.21  tff(c_135, plain, (![A_41, C_42, B_43]: (k4_xboole_0(A_41, k4_xboole_0(C_42, B_43))=A_41 | ~r1_tarski(A_41, B_43))), inference(resolution, [status(thm)], [c_54, c_6])).
% 5.97/2.21  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, k4_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.97/2.21  tff(c_174, plain, (![A_44, A_45, C_46, B_47]: (r1_xboole_0(A_44, A_45) | ~r1_tarski(A_44, k4_xboole_0(C_46, B_47)) | ~r1_tarski(A_45, B_47))), inference(superposition, [status(thm), theory('equality')], [c_135, c_10])).
% 5.97/2.21  tff(c_187, plain, (![C_46, B_47, A_45]: (r1_xboole_0(k4_xboole_0(C_46, B_47), A_45) | ~r1_tarski(A_45, B_47))), inference(resolution, [status(thm)], [c_37, c_174])).
% 5.97/2.21  tff(c_12, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.97/2.21  tff(c_16, plain, (![C_16, A_14, B_15]: (k7_relat_1(C_16, k6_subset_1(A_14, B_15))=k6_subset_1(C_16, k7_relat_1(C_16, B_15)) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.97/2.21  tff(c_221, plain, (![C_54, A_55, B_56]: (k7_relat_1(C_54, k4_xboole_0(A_55, B_56))=k4_xboole_0(C_54, k7_relat_1(C_54, B_56)) | ~r1_tarski(k1_relat_1(C_54), A_55) | ~v1_relat_1(C_54))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16])).
% 5.97/2.21  tff(c_1690, plain, (![C_168, B_169]: (k7_relat_1(C_168, k4_xboole_0(k1_relat_1(C_168), B_169))=k4_xboole_0(C_168, k7_relat_1(C_168, B_169)) | ~v1_relat_1(C_168))), inference(resolution, [status(thm)], [c_37, c_221])).
% 5.97/2.21  tff(c_14, plain, (![C_13, A_11, B_12]: (k7_relat_1(k7_relat_1(C_13, A_11), B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.97/2.21  tff(c_5788, plain, (![C_351, B_352, B_353]: (k7_relat_1(k4_xboole_0(C_351, k7_relat_1(C_351, B_352)), B_353)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(C_351), B_352), B_353) | ~v1_relat_1(C_351) | ~v1_relat_1(C_351))), inference(superposition, [status(thm), theory('equality')], [c_1690, c_14])).
% 5.97/2.21  tff(c_6197, plain, (![C_369, B_370, A_371]: (k7_relat_1(k4_xboole_0(C_369, k7_relat_1(C_369, B_370)), A_371)=k1_xboole_0 | ~v1_relat_1(C_369) | ~r1_tarski(A_371, B_370))), inference(resolution, [status(thm)], [c_187, c_5788])).
% 5.97/2.21  tff(c_18, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.97/2.21  tff(c_23, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 5.97/2.21  tff(c_6257, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6197, c_23])).
% 5.97/2.21  tff(c_6324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_6257])).
% 5.97/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.21  
% 5.97/2.21  Inference rules
% 5.97/2.21  ----------------------
% 5.97/2.21  #Ref     : 0
% 5.97/2.21  #Sup     : 1906
% 5.97/2.21  #Fact    : 0
% 5.97/2.21  #Define  : 0
% 5.97/2.21  #Split   : 7
% 5.97/2.21  #Chain   : 0
% 5.97/2.21  #Close   : 0
% 5.97/2.21  
% 5.97/2.21  Ordering : KBO
% 5.97/2.21  
% 5.97/2.21  Simplification rules
% 5.97/2.21  ----------------------
% 5.97/2.21  #Subsume      : 758
% 5.97/2.21  #Demod        : 157
% 5.97/2.21  #Tautology    : 240
% 5.97/2.21  #SimpNegUnit  : 0
% 5.97/2.21  #BackRed      : 0
% 5.97/2.21  
% 5.97/2.21  #Partial instantiations: 0
% 5.97/2.21  #Strategies tried      : 1
% 5.97/2.21  
% 5.97/2.21  Timing (in seconds)
% 5.97/2.21  ----------------------
% 5.97/2.22  Preprocessing        : 0.27
% 5.97/2.22  Parsing              : 0.14
% 5.97/2.22  CNF conversion       : 0.01
% 5.97/2.22  Main loop            : 1.18
% 5.97/2.22  Inferencing          : 0.37
% 5.97/2.22  Reduction            : 0.29
% 5.97/2.22  Demodulation         : 0.20
% 5.97/2.22  BG Simplification    : 0.04
% 5.97/2.22  Subsumption          : 0.40
% 5.97/2.22  Abstraction          : 0.05
% 5.97/2.22  MUC search           : 0.00
% 5.97/2.22  Cooper               : 0.00
% 5.97/2.22  Total                : 1.47
% 5.97/2.22  Index Insertion      : 0.00
% 5.97/2.22  Index Deletion       : 0.00
% 5.97/2.22  Index Matching       : 0.00
% 5.97/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
