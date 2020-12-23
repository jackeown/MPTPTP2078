%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:44 EST 2020

% Result     : Theorem 7.24s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 (  73 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_xboole_0(A_26,k4_xboole_0(C_27,B_28))
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [C_27,B_28,A_26] :
      ( r1_xboole_0(k4_xboole_0(C_27,B_28),A_26)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [B_36,A_37] :
      ( v4_relat_1(B_36,A_37)
      | ~ r1_tarski(k1_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [B_38,B_39] :
      ( v4_relat_1(B_38,k2_xboole_0(k1_relat_1(B_38),B_39))
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    ! [B_38,B_39] :
      ( k7_relat_1(B_38,k2_xboole_0(k1_relat_1(B_38),B_39)) = B_38
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_58,c_18])).

tff(c_8,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] :
      ( k6_subset_1(k7_relat_1(C_14,A_12),k7_relat_1(C_14,B_13)) = k7_relat_1(C_14,k6_subset_1(A_12,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [C_45,A_46,B_47] :
      ( k4_xboole_0(k7_relat_1(C_45,A_46),k7_relat_1(C_45,B_47)) = k7_relat_1(C_45,k4_xboole_0(A_46,B_47))
      | ~ v1_relat_1(C_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_14])).

tff(c_242,plain,(
    ! [B_74,B_75,B_76] :
      ( k7_relat_1(B_74,k4_xboole_0(k2_xboole_0(k1_relat_1(B_74),B_75),B_76)) = k4_xboole_0(B_74,k7_relat_1(B_74,B_76))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_98])).

tff(c_16,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_17,A_15),B_16) = k1_xboole_0
      | ~ r1_xboole_0(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5461,plain,(
    ! [B_446,B_447,B_448,B_449] :
      ( k7_relat_1(k4_xboole_0(B_446,k7_relat_1(B_446,B_447)),B_448) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(B_446),B_449),B_447),B_448)
      | ~ v1_relat_1(B_446)
      | ~ v1_relat_1(B_446)
      | ~ v1_relat_1(B_446) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_16])).

tff(c_5485,plain,(
    ! [B_450,B_451,A_452] :
      ( k7_relat_1(k4_xboole_0(B_450,k7_relat_1(B_450,B_451)),A_452) = k1_xboole_0
      | ~ v1_relat_1(B_450)
      | ~ r1_tarski(A_452,B_451) ) ),
    inference(resolution,[status(thm)],[c_41,c_5461])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_25,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_5691,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5485,c_25])).

tff(c_5834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_5691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.24/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.24/2.56  
% 7.24/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.24/2.56  %$ v4_relat_1 > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.24/2.56  
% 7.24/2.56  %Foreground sorts:
% 7.24/2.56  
% 7.24/2.56  
% 7.24/2.56  %Background operators:
% 7.24/2.56  
% 7.24/2.56  
% 7.24/2.56  %Foreground operators:
% 7.24/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.24/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.24/2.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.24/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.24/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.24/2.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.24/2.56  tff('#skF_2', type, '#skF_2': $i).
% 7.24/2.56  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.24/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.24/2.56  tff('#skF_1', type, '#skF_1': $i).
% 7.24/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.24/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.24/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.24/2.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.24/2.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.24/2.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.24/2.56  
% 7.24/2.57  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 7.24/2.57  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 7.24/2.57  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.24/2.57  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.24/2.57  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.24/2.57  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.24/2.57  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.24/2.57  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 7.24/2.57  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 7.24/2.57  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.24/2.57  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.24/2.57  tff(c_38, plain, (![A_26, C_27, B_28]: (r1_xboole_0(A_26, k4_xboole_0(C_27, B_28)) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.24/2.57  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.24/2.57  tff(c_41, plain, (![C_27, B_28, A_26]: (r1_xboole_0(k4_xboole_0(C_27, B_28), A_26) | ~r1_tarski(A_26, B_28))), inference(resolution, [status(thm)], [c_38, c_2])).
% 7.24/2.57  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.24/2.57  tff(c_48, plain, (![B_36, A_37]: (v4_relat_1(B_36, A_37) | ~r1_tarski(k1_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.24/2.57  tff(c_58, plain, (![B_38, B_39]: (v4_relat_1(B_38, k2_xboole_0(k1_relat_1(B_38), B_39)) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_4, c_48])).
% 7.24/2.57  tff(c_18, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.24/2.57  tff(c_62, plain, (![B_38, B_39]: (k7_relat_1(B_38, k2_xboole_0(k1_relat_1(B_38), B_39))=B_38 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_58, c_18])).
% 7.24/2.57  tff(c_8, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.24/2.57  tff(c_14, plain, (![C_14, A_12, B_13]: (k6_subset_1(k7_relat_1(C_14, A_12), k7_relat_1(C_14, B_13))=k7_relat_1(C_14, k6_subset_1(A_12, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.24/2.57  tff(c_98, plain, (![C_45, A_46, B_47]: (k4_xboole_0(k7_relat_1(C_45, A_46), k7_relat_1(C_45, B_47))=k7_relat_1(C_45, k4_xboole_0(A_46, B_47)) | ~v1_relat_1(C_45))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_14])).
% 7.24/2.57  tff(c_242, plain, (![B_74, B_75, B_76]: (k7_relat_1(B_74, k4_xboole_0(k2_xboole_0(k1_relat_1(B_74), B_75), B_76))=k4_xboole_0(B_74, k7_relat_1(B_74, B_76)) | ~v1_relat_1(B_74) | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_62, c_98])).
% 7.24/2.57  tff(c_16, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k1_xboole_0 | ~r1_xboole_0(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.24/2.57  tff(c_5461, plain, (![B_446, B_447, B_448, B_449]: (k7_relat_1(k4_xboole_0(B_446, k7_relat_1(B_446, B_447)), B_448)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(B_446), B_449), B_447), B_448) | ~v1_relat_1(B_446) | ~v1_relat_1(B_446) | ~v1_relat_1(B_446))), inference(superposition, [status(thm), theory('equality')], [c_242, c_16])).
% 7.24/2.57  tff(c_5485, plain, (![B_450, B_451, A_452]: (k7_relat_1(k4_xboole_0(B_450, k7_relat_1(B_450, B_451)), A_452)=k1_xboole_0 | ~v1_relat_1(B_450) | ~r1_tarski(A_452, B_451))), inference(resolution, [status(thm)], [c_41, c_5461])).
% 7.24/2.57  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.24/2.57  tff(c_25, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 7.24/2.57  tff(c_5691, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5485, c_25])).
% 7.24/2.57  tff(c_5834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_5691])).
% 7.24/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.24/2.57  
% 7.24/2.57  Inference rules
% 7.24/2.57  ----------------------
% 7.24/2.57  #Ref     : 0
% 7.24/2.57  #Sup     : 1893
% 7.24/2.57  #Fact    : 0
% 7.24/2.57  #Define  : 0
% 7.24/2.57  #Split   : 4
% 7.24/2.57  #Chain   : 0
% 7.24/2.57  #Close   : 0
% 7.24/2.57  
% 7.24/2.57  Ordering : KBO
% 7.24/2.57  
% 7.24/2.57  Simplification rules
% 7.24/2.57  ----------------------
% 7.24/2.57  #Subsume      : 470
% 7.24/2.57  #Demod        : 5
% 7.24/2.57  #Tautology    : 90
% 7.24/2.57  #SimpNegUnit  : 0
% 7.24/2.57  #BackRed      : 0
% 7.24/2.57  
% 7.24/2.57  #Partial instantiations: 0
% 7.24/2.57  #Strategies tried      : 1
% 7.24/2.57  
% 7.24/2.57  Timing (in seconds)
% 7.24/2.57  ----------------------
% 7.24/2.58  Preprocessing        : 0.28
% 7.24/2.58  Parsing              : 0.15
% 7.24/2.58  CNF conversion       : 0.02
% 7.24/2.58  Main loop            : 1.54
% 7.24/2.58  Inferencing          : 0.54
% 7.24/2.58  Reduction            : 0.37
% 7.24/2.58  Demodulation         : 0.24
% 7.24/2.58  BG Simplification    : 0.07
% 7.24/2.58  Subsumption          : 0.47
% 7.24/2.58  Abstraction          : 0.08
% 7.24/2.58  MUC search           : 0.00
% 7.24/2.58  Cooper               : 0.00
% 7.24/2.58  Total                : 1.85
% 7.24/2.58  Index Insertion      : 0.00
% 7.24/2.58  Index Deletion       : 0.00
% 7.24/2.58  Index Matching       : 0.00
% 7.24/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
