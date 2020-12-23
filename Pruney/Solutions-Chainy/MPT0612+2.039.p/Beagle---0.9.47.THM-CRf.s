%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  65 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_xboole_0(A_24,k4_xboole_0(C_25,B_26))
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [C_25,B_26,A_24] :
      ( r1_xboole_0(k4_xboole_0(C_25,B_26),A_24)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [B_30,A_31] :
      ( k7_relat_1(B_30,A_31) = B_30
      | ~ r1_tarski(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    ! [B_30,B_4] :
      ( k7_relat_1(B_30,k2_xboole_0(k1_relat_1(B_30),B_4)) = B_30
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_4,c_42])).

tff(c_8,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [C_12,A_10,B_11] :
      ( k6_subset_1(k7_relat_1(C_12,A_10),k7_relat_1(C_12,B_11)) = k7_relat_1(C_12,k6_subset_1(A_10,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [C_37,A_38,B_39] :
      ( k4_xboole_0(k7_relat_1(C_37,A_38),k7_relat_1(C_37,B_39)) = k7_relat_1(C_37,k4_xboole_0(A_38,B_39))
      | ~ v1_relat_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_227,plain,(
    ! [B_66,B_67,B_68] :
      ( k7_relat_1(B_66,k4_xboole_0(k2_xboole_0(k1_relat_1(B_66),B_67),B_68)) = k4_xboole_0(B_66,k7_relat_1(B_66,B_68))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_83])).

tff(c_12,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3825,plain,(
    ! [B_330,B_331,B_332,B_333] :
      ( k7_relat_1(k4_xboole_0(B_330,k7_relat_1(B_330,B_331)),B_332) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(B_330),B_333),B_331),B_332)
      | ~ v1_relat_1(B_330)
      | ~ v1_relat_1(B_330)
      | ~ v1_relat_1(B_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_12])).

tff(c_3845,plain,(
    ! [B_334,B_335,A_336] :
      ( k7_relat_1(k4_xboole_0(B_334,k7_relat_1(B_334,B_335)),A_336) = k1_xboole_0
      | ~ v1_relat_1(B_334)
      | ~ r1_tarski(A_336,B_335) ) ),
    inference(resolution,[status(thm)],[c_37,c_3825])).

tff(c_16,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_4012,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3845,c_21])).

tff(c_4152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_4012])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.15  
% 5.85/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.15  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.85/2.15  
% 5.85/2.15  %Foreground sorts:
% 5.85/2.15  
% 5.85/2.15  
% 5.85/2.15  %Background operators:
% 5.85/2.15  
% 5.85/2.15  
% 5.85/2.15  %Foreground operators:
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.85/2.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.85/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.85/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.85/2.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.85/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.85/2.15  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.85/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.85/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.85/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.85/2.15  
% 5.85/2.16  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 5.85/2.16  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.85/2.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.85/2.16  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.85/2.16  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.85/2.16  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.85/2.16  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 5.85/2.16  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 5.85/2.16  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.85/2.16  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.85/2.16  tff(c_34, plain, (![A_24, C_25, B_26]: (r1_xboole_0(A_24, k4_xboole_0(C_25, B_26)) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.85/2.16  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.85/2.16  tff(c_37, plain, (![C_25, B_26, A_24]: (r1_xboole_0(k4_xboole_0(C_25, B_26), A_24) | ~r1_tarski(A_24, B_26))), inference(resolution, [status(thm)], [c_34, c_2])).
% 5.85/2.16  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.85/2.16  tff(c_42, plain, (![B_30, A_31]: (k7_relat_1(B_30, A_31)=B_30 | ~r1_tarski(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.85/2.16  tff(c_47, plain, (![B_30, B_4]: (k7_relat_1(B_30, k2_xboole_0(k1_relat_1(B_30), B_4))=B_30 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_4, c_42])).
% 5.85/2.16  tff(c_8, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.85/2.16  tff(c_10, plain, (![C_12, A_10, B_11]: (k6_subset_1(k7_relat_1(C_12, A_10), k7_relat_1(C_12, B_11))=k7_relat_1(C_12, k6_subset_1(A_10, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.85/2.16  tff(c_83, plain, (![C_37, A_38, B_39]: (k4_xboole_0(k7_relat_1(C_37, A_38), k7_relat_1(C_37, B_39))=k7_relat_1(C_37, k4_xboole_0(A_38, B_39)) | ~v1_relat_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 5.85/2.16  tff(c_227, plain, (![B_66, B_67, B_68]: (k7_relat_1(B_66, k4_xboole_0(k2_xboole_0(k1_relat_1(B_66), B_67), B_68))=k4_xboole_0(B_66, k7_relat_1(B_66, B_68)) | ~v1_relat_1(B_66) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_47, c_83])).
% 5.85/2.16  tff(c_12, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.85/2.16  tff(c_3825, plain, (![B_330, B_331, B_332, B_333]: (k7_relat_1(k4_xboole_0(B_330, k7_relat_1(B_330, B_331)), B_332)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(B_330), B_333), B_331), B_332) | ~v1_relat_1(B_330) | ~v1_relat_1(B_330) | ~v1_relat_1(B_330))), inference(superposition, [status(thm), theory('equality')], [c_227, c_12])).
% 5.85/2.16  tff(c_3845, plain, (![B_334, B_335, A_336]: (k7_relat_1(k4_xboole_0(B_334, k7_relat_1(B_334, B_335)), A_336)=k1_xboole_0 | ~v1_relat_1(B_334) | ~r1_tarski(A_336, B_335))), inference(resolution, [status(thm)], [c_37, c_3825])).
% 5.85/2.16  tff(c_16, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.85/2.16  tff(c_21, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 5.85/2.16  tff(c_4012, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3845, c_21])).
% 5.85/2.16  tff(c_4152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_4012])).
% 5.85/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.16  
% 5.85/2.16  Inference rules
% 5.85/2.16  ----------------------
% 5.85/2.16  #Ref     : 0
% 5.85/2.16  #Sup     : 1329
% 5.85/2.16  #Fact    : 0
% 5.85/2.16  #Define  : 0
% 5.85/2.16  #Split   : 4
% 5.85/2.16  #Chain   : 0
% 5.85/2.16  #Close   : 0
% 5.85/2.16  
% 5.85/2.16  Ordering : KBO
% 5.85/2.16  
% 5.85/2.16  Simplification rules
% 5.85/2.16  ----------------------
% 5.85/2.16  #Subsume      : 314
% 5.85/2.16  #Demod        : 5
% 5.85/2.16  #Tautology    : 89
% 5.85/2.16  #SimpNegUnit  : 0
% 5.85/2.16  #BackRed      : 0
% 5.85/2.16  
% 5.85/2.16  #Partial instantiations: 0
% 5.85/2.16  #Strategies tried      : 1
% 5.85/2.16  
% 5.85/2.16  Timing (in seconds)
% 5.85/2.16  ----------------------
% 5.85/2.16  Preprocessing        : 0.27
% 5.85/2.16  Parsing              : 0.14
% 5.85/2.16  CNF conversion       : 0.02
% 5.85/2.16  Main loop            : 1.10
% 5.85/2.16  Inferencing          : 0.40
% 5.85/2.16  Reduction            : 0.27
% 5.85/2.16  Demodulation         : 0.18
% 5.85/2.16  BG Simplification    : 0.06
% 5.85/2.16  Subsumption          : 0.31
% 5.85/2.16  Abstraction          : 0.06
% 5.85/2.16  MUC search           : 0.00
% 5.85/2.16  Cooper               : 0.00
% 5.85/2.16  Total                : 1.39
% 5.85/2.16  Index Insertion      : 0.00
% 5.85/2.16  Index Deletion       : 0.00
% 5.85/2.16  Index Matching       : 0.00
% 5.85/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
