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
% DateTime   : Thu Dec  3 10:02:43 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  75 expanded)
%              Number of equality atoms :   18 (  28 expanded)
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

tff(f_65,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(C_15,k6_subset_1(A_13,B_14)) = k6_subset_1(C_15,k7_relat_1(C_15,B_14))
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65,plain,(
    ! [C_32,A_33,B_34] :
      ( k7_relat_1(C_32,k4_xboole_0(A_33,B_34)) = k4_xboole_0(C_32,k7_relat_1(C_32,B_34))
      | ~ r1_tarski(k1_relat_1(C_32),A_33)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_72,plain,(
    ! [C_35,B_36] :
      ( k7_relat_1(C_35,k4_xboole_0(k1_relat_1(C_35),B_36)) = k4_xboole_0(C_35,k7_relat_1(C_35,B_36))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [C_35,B_36] :
      ( v1_relat_1(k4_xboole_0(C_35,k7_relat_1(C_35,B_36)))
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_12])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k6_subset_1(B_17,k7_relat_1(B_17,A_16))) = k6_subset_1(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [B_30,A_31] :
      ( k1_relat_1(k4_xboole_0(B_30,k7_relat_1(B_30,A_31))) = k4_xboole_0(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_18])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k7_relat_1(A_10,B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,k1_relat_1(A_10))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_94,plain,(
    ! [B_39,A_40,B_41] :
      ( k7_relat_1(k4_xboole_0(B_39,k7_relat_1(B_39,A_40)),B_41) = k1_xboole_0
      | ~ r1_xboole_0(B_41,k4_xboole_0(k1_relat_1(B_39),A_40))
      | ~ v1_relat_1(k4_xboole_0(B_39,k7_relat_1(B_39,A_40)))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_14])).

tff(c_109,plain,(
    ! [B_46,B_47,A_48] :
      ( k7_relat_1(k4_xboole_0(B_46,k7_relat_1(B_46,B_47)),A_48) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_46,k7_relat_1(B_46,B_47)))
      | ~ v1_relat_1(B_46)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_94])).

tff(c_115,plain,(
    ! [C_49,B_50,A_51] :
      ( k7_relat_1(k4_xboole_0(C_49,k7_relat_1(C_49,B_50)),A_51) = k1_xboole_0
      | ~ r1_tarski(A_51,B_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_81,c_109])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_27,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_140,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_27])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.19  
% 1.86/1.19  %Foreground sorts:
% 1.86/1.19  
% 1.86/1.19  
% 1.86/1.19  %Background operators:
% 1.86/1.19  
% 1.86/1.19  
% 1.86/1.19  %Foreground operators:
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.19  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.86/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.19  
% 1.86/1.21  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 1.86/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.86/1.21  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.86/1.21  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 1.86/1.21  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.86/1.21  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.86/1.21  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 1.86/1.21  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 1.86/1.21  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.21  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.21  tff(c_10, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.21  tff(c_16, plain, (![C_15, A_13, B_14]: (k7_relat_1(C_15, k6_subset_1(A_13, B_14))=k6_subset_1(C_15, k7_relat_1(C_15, B_14)) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.86/1.21  tff(c_65, plain, (![C_32, A_33, B_34]: (k7_relat_1(C_32, k4_xboole_0(A_33, B_34))=k4_xboole_0(C_32, k7_relat_1(C_32, B_34)) | ~r1_tarski(k1_relat_1(C_32), A_33) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 1.86/1.21  tff(c_72, plain, (![C_35, B_36]: (k7_relat_1(C_35, k4_xboole_0(k1_relat_1(C_35), B_36))=k4_xboole_0(C_35, k7_relat_1(C_35, B_36)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_6, c_65])).
% 1.86/1.21  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.21  tff(c_81, plain, (![C_35, B_36]: (v1_relat_1(k4_xboole_0(C_35, k7_relat_1(C_35, B_36))) | ~v1_relat_1(C_35) | ~v1_relat_1(C_35))), inference(superposition, [status(thm), theory('equality')], [c_72, c_12])).
% 1.86/1.21  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.21  tff(c_18, plain, (![B_17, A_16]: (k1_relat_1(k6_subset_1(B_17, k7_relat_1(B_17, A_16)))=k6_subset_1(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.86/1.21  tff(c_53, plain, (![B_30, A_31]: (k1_relat_1(k4_xboole_0(B_30, k7_relat_1(B_30, A_31)))=k4_xboole_0(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_18])).
% 1.86/1.21  tff(c_14, plain, (![A_10, B_12]: (k7_relat_1(A_10, B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, k1_relat_1(A_10)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.21  tff(c_94, plain, (![B_39, A_40, B_41]: (k7_relat_1(k4_xboole_0(B_39, k7_relat_1(B_39, A_40)), B_41)=k1_xboole_0 | ~r1_xboole_0(B_41, k4_xboole_0(k1_relat_1(B_39), A_40)) | ~v1_relat_1(k4_xboole_0(B_39, k7_relat_1(B_39, A_40))) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_53, c_14])).
% 1.86/1.21  tff(c_109, plain, (![B_46, B_47, A_48]: (k7_relat_1(k4_xboole_0(B_46, k7_relat_1(B_46, B_47)), A_48)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_46, k7_relat_1(B_46, B_47))) | ~v1_relat_1(B_46) | ~r1_tarski(A_48, B_47))), inference(resolution, [status(thm)], [c_8, c_94])).
% 1.86/1.21  tff(c_115, plain, (![C_49, B_50, A_51]: (k7_relat_1(k4_xboole_0(C_49, k7_relat_1(C_49, B_50)), A_51)=k1_xboole_0 | ~r1_tarski(A_51, B_50) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_81, c_109])).
% 1.86/1.21  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.21  tff(c_27, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.86/1.21  tff(c_140, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_27])).
% 1.86/1.21  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_140])).
% 1.86/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  Inference rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Ref     : 0
% 1.86/1.21  #Sup     : 34
% 1.86/1.21  #Fact    : 0
% 1.86/1.21  #Define  : 0
% 1.86/1.21  #Split   : 1
% 1.86/1.21  #Chain   : 0
% 1.86/1.21  #Close   : 0
% 1.86/1.21  
% 1.86/1.21  Ordering : KBO
% 1.86/1.21  
% 1.86/1.21  Simplification rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Subsume      : 1
% 1.86/1.21  #Demod        : 9
% 1.86/1.21  #Tautology    : 9
% 1.86/1.21  #SimpNegUnit  : 0
% 1.86/1.21  #BackRed      : 0
% 1.86/1.21  
% 1.86/1.21  #Partial instantiations: 0
% 1.86/1.21  #Strategies tried      : 1
% 1.86/1.21  
% 1.86/1.21  Timing (in seconds)
% 1.86/1.21  ----------------------
% 1.86/1.21  Preprocessing        : 0.29
% 1.86/1.21  Parsing              : 0.16
% 1.86/1.21  CNF conversion       : 0.02
% 1.86/1.21  Main loop            : 0.16
% 1.86/1.21  Inferencing          : 0.06
% 1.86/1.21  Reduction            : 0.04
% 1.86/1.21  Demodulation         : 0.03
% 1.86/1.21  BG Simplification    : 0.01
% 1.86/1.21  Subsumption          : 0.03
% 1.86/1.21  Abstraction          : 0.01
% 1.86/1.21  MUC search           : 0.00
% 1.86/1.21  Cooper               : 0.00
% 1.86/1.21  Total                : 0.47
% 1.86/1.21  Index Insertion      : 0.00
% 1.86/1.21  Index Deletion       : 0.00
% 1.86/1.21  Index Matching       : 0.00
% 1.86/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
