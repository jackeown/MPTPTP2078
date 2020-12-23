%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:43 EST 2020

% Result     : Theorem 15.60s
% Output     : CNFRefutation 15.70s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 118 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,k4_xboole_0(C_28,B_29))
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_30,C_31,B_32] :
      ( k4_xboole_0(A_30,k4_xboole_0(C_31,B_32)) = A_30
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(resolution,[status(thm)],[c_57,c_8])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_148,plain,(
    ! [A_42,A_43,C_44,B_45] :
      ( r1_xboole_0(A_42,A_43)
      | ~ r1_tarski(A_42,k4_xboole_0(C_44,B_45))
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_157,plain,(
    ! [C_46,B_47,A_48] :
      ( r1_xboole_0(k4_xboole_0(C_46,B_47),A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_168,plain,(
    ! [C_49,B_50,A_51] :
      ( k4_xboole_0(k4_xboole_0(C_49,B_50),A_51) = k4_xboole_0(C_49,B_50)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(resolution,[status(thm)],[c_157,c_8])).

tff(c_156,plain,(
    ! [C_44,B_45,A_43] :
      ( r1_xboole_0(k4_xboole_0(C_44,B_45),A_43)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_294,plain,(
    ! [C_64,B_65,A_66,A_67] :
      ( r1_xboole_0(k4_xboole_0(C_64,B_65),A_66)
      | ~ r1_tarski(A_66,A_67)
      | ~ r1_tarski(A_67,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_156])).

tff(c_300,plain,(
    ! [C_64,B_65] :
      ( r1_xboole_0(k4_xboole_0(C_64,B_65),'#skF_1')
      | ~ r1_tarski('#skF_2',B_65) ) ),
    inference(resolution,[status(thm)],[c_24,c_294])).

tff(c_80,plain,(
    ! [B_33,A_34] :
      ( k7_relat_1(B_33,A_34) = B_33
      | ~ r1_tarski(k1_relat_1(B_33),A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [B_33] :
      ( k7_relat_1(B_33,k1_relat_1(B_33)) = B_33
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_14,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_12,A_10,B_11] :
      ( k6_subset_1(k7_relat_1(C_12,A_10),k7_relat_1(C_12,B_11)) = k7_relat_1(C_12,k6_subset_1(A_10,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    ! [C_39,A_40,B_41] :
      ( k4_xboole_0(k7_relat_1(C_39,A_40),k7_relat_1(C_39,B_41)) = k7_relat_1(C_39,k4_xboole_0(A_40,B_41))
      | ~ v1_relat_1(C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16])).

tff(c_1578,plain,(
    ! [B_179,B_180] :
      ( k7_relat_1(B_179,k4_xboole_0(k1_relat_1(B_179),B_180)) = k4_xboole_0(B_179,k7_relat_1(B_179,B_180))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(B_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_121])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26028,plain,(
    ! [B_1074,B_1075,B_1076] :
      ( k7_relat_1(k4_xboole_0(B_1074,k7_relat_1(B_1074,B_1075)),B_1076) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(B_1074),B_1075),B_1076)
      | ~ v1_relat_1(B_1074)
      | ~ v1_relat_1(B_1074)
      | ~ v1_relat_1(B_1074) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_18])).

tff(c_26266,plain,(
    ! [B_1081,B_1082] :
      ( k7_relat_1(k4_xboole_0(B_1081,k7_relat_1(B_1081,B_1082)),'#skF_1') = k1_xboole_0
      | ~ v1_relat_1(B_1081)
      | ~ r1_tarski('#skF_2',B_1082) ) ),
    inference(resolution,[status(thm)],[c_300,c_26028])).

tff(c_22,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_27,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_26400,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26266,c_27])).

tff(c_26494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26,c_26400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.60/7.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.60/7.65  
% 15.60/7.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.60/7.65  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.60/7.65  
% 15.60/7.65  %Foreground sorts:
% 15.60/7.65  
% 15.60/7.65  
% 15.60/7.65  %Background operators:
% 15.60/7.65  
% 15.60/7.65  
% 15.60/7.65  %Foreground operators:
% 15.60/7.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.60/7.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.60/7.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.60/7.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.60/7.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.60/7.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.60/7.65  tff('#skF_2', type, '#skF_2': $i).
% 15.60/7.65  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 15.60/7.65  tff('#skF_3', type, '#skF_3': $i).
% 15.60/7.65  tff('#skF_1', type, '#skF_1': $i).
% 15.60/7.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.60/7.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.60/7.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.60/7.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.60/7.65  
% 15.70/7.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.70/7.66  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 15.70/7.66  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 15.70/7.66  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.70/7.66  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 15.70/7.66  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 15.70/7.66  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 15.70/7.66  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 15.70/7.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.70/7.66  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.70/7.66  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.70/7.66  tff(c_57, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, k4_xboole_0(C_28, B_29)) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.70/7.66  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.70/7.66  tff(c_62, plain, (![A_30, C_31, B_32]: (k4_xboole_0(A_30, k4_xboole_0(C_31, B_32))=A_30 | ~r1_tarski(A_30, B_32))), inference(resolution, [status(thm)], [c_57, c_8])).
% 15.70/7.66  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.70/7.66  tff(c_148, plain, (![A_42, A_43, C_44, B_45]: (r1_xboole_0(A_42, A_43) | ~r1_tarski(A_42, k4_xboole_0(C_44, B_45)) | ~r1_tarski(A_43, B_45))), inference(superposition, [status(thm), theory('equality')], [c_62, c_12])).
% 15.70/7.66  tff(c_157, plain, (![C_46, B_47, A_48]: (r1_xboole_0(k4_xboole_0(C_46, B_47), A_48) | ~r1_tarski(A_48, B_47))), inference(resolution, [status(thm)], [c_6, c_148])).
% 15.70/7.66  tff(c_168, plain, (![C_49, B_50, A_51]: (k4_xboole_0(k4_xboole_0(C_49, B_50), A_51)=k4_xboole_0(C_49, B_50) | ~r1_tarski(A_51, B_50))), inference(resolution, [status(thm)], [c_157, c_8])).
% 15.70/7.66  tff(c_156, plain, (![C_44, B_45, A_43]: (r1_xboole_0(k4_xboole_0(C_44, B_45), A_43) | ~r1_tarski(A_43, B_45))), inference(resolution, [status(thm)], [c_6, c_148])).
% 15.70/7.66  tff(c_294, plain, (![C_64, B_65, A_66, A_67]: (r1_xboole_0(k4_xboole_0(C_64, B_65), A_66) | ~r1_tarski(A_66, A_67) | ~r1_tarski(A_67, B_65))), inference(superposition, [status(thm), theory('equality')], [c_168, c_156])).
% 15.70/7.66  tff(c_300, plain, (![C_64, B_65]: (r1_xboole_0(k4_xboole_0(C_64, B_65), '#skF_1') | ~r1_tarski('#skF_2', B_65))), inference(resolution, [status(thm)], [c_24, c_294])).
% 15.70/7.66  tff(c_80, plain, (![B_33, A_34]: (k7_relat_1(B_33, A_34)=B_33 | ~r1_tarski(k1_relat_1(B_33), A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.70/7.66  tff(c_85, plain, (![B_33]: (k7_relat_1(B_33, k1_relat_1(B_33))=B_33 | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_6, c_80])).
% 15.70/7.66  tff(c_14, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.70/7.66  tff(c_16, plain, (![C_12, A_10, B_11]: (k6_subset_1(k7_relat_1(C_12, A_10), k7_relat_1(C_12, B_11))=k7_relat_1(C_12, k6_subset_1(A_10, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.70/7.66  tff(c_121, plain, (![C_39, A_40, B_41]: (k4_xboole_0(k7_relat_1(C_39, A_40), k7_relat_1(C_39, B_41))=k7_relat_1(C_39, k4_xboole_0(A_40, B_41)) | ~v1_relat_1(C_39))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16])).
% 15.70/7.66  tff(c_1578, plain, (![B_179, B_180]: (k7_relat_1(B_179, k4_xboole_0(k1_relat_1(B_179), B_180))=k4_xboole_0(B_179, k7_relat_1(B_179, B_180)) | ~v1_relat_1(B_179) | ~v1_relat_1(B_179))), inference(superposition, [status(thm), theory('equality')], [c_85, c_121])).
% 15.70/7.66  tff(c_18, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.70/7.66  tff(c_26028, plain, (![B_1074, B_1075, B_1076]: (k7_relat_1(k4_xboole_0(B_1074, k7_relat_1(B_1074, B_1075)), B_1076)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(B_1074), B_1075), B_1076) | ~v1_relat_1(B_1074) | ~v1_relat_1(B_1074) | ~v1_relat_1(B_1074))), inference(superposition, [status(thm), theory('equality')], [c_1578, c_18])).
% 15.70/7.66  tff(c_26266, plain, (![B_1081, B_1082]: (k7_relat_1(k4_xboole_0(B_1081, k7_relat_1(B_1081, B_1082)), '#skF_1')=k1_xboole_0 | ~v1_relat_1(B_1081) | ~r1_tarski('#skF_2', B_1082))), inference(resolution, [status(thm)], [c_300, c_26028])).
% 15.70/7.66  tff(c_22, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.70/7.66  tff(c_27, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 15.70/7.66  tff(c_26400, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26266, c_27])).
% 15.70/7.66  tff(c_26494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_26, c_26400])).
% 15.70/7.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.70/7.66  
% 15.70/7.66  Inference rules
% 15.70/7.66  ----------------------
% 15.70/7.66  #Ref     : 0
% 15.70/7.66  #Sup     : 8704
% 15.70/7.66  #Fact    : 0
% 15.70/7.66  #Define  : 0
% 15.70/7.66  #Split   : 32
% 15.70/7.66  #Chain   : 0
% 15.70/7.66  #Close   : 0
% 15.70/7.66  
% 15.70/7.66  Ordering : KBO
% 15.70/7.66  
% 15.70/7.66  Simplification rules
% 15.70/7.66  ----------------------
% 15.70/7.66  #Subsume      : 3442
% 15.70/7.66  #Demod        : 356
% 15.70/7.66  #Tautology    : 195
% 15.70/7.66  #SimpNegUnit  : 18
% 15.70/7.66  #BackRed      : 18
% 15.70/7.66  
% 15.70/7.66  #Partial instantiations: 0
% 15.70/7.66  #Strategies tried      : 1
% 15.70/7.66  
% 15.70/7.66  Timing (in seconds)
% 15.70/7.66  ----------------------
% 15.70/7.66  Preprocessing        : 0.27
% 15.70/7.66  Parsing              : 0.14
% 15.70/7.66  CNF conversion       : 0.02
% 15.70/7.66  Main loop            : 6.63
% 15.70/7.66  Inferencing          : 1.21
% 15.70/7.66  Reduction            : 1.03
% 15.70/7.66  Demodulation         : 0.66
% 15.70/7.67  BG Simplification    : 0.19
% 15.70/7.67  Subsumption          : 3.86
% 15.70/7.67  Abstraction          : 0.23
% 15.70/7.67  MUC search           : 0.00
% 15.70/7.67  Cooper               : 0.00
% 15.70/7.67  Total                : 6.93
% 15.70/7.67  Index Insertion      : 0.00
% 15.70/7.67  Index Deletion       : 0.00
% 15.70/7.67  Index Matching       : 0.00
% 15.70/7.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
