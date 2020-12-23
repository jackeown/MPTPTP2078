%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:42 EST 2020

% Result     : Theorem 26.85s
% Output     : CNFRefutation 26.85s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 (  75 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_xboole_0(A_25,k4_xboole_0(C_26,B_27))
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [C_26,B_27,A_25] :
      ( r1_xboole_0(k4_xboole_0(C_26,B_27),A_25)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [B_35,A_36] :
      ( v4_relat_1(B_35,A_36)
      | ~ r1_tarski(k1_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    ! [B_35] :
      ( v4_relat_1(B_35,k1_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_77,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = B_38
      | ~ v4_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [B_35] :
      ( k7_relat_1(B_35,k1_relat_1(B_35)) = B_35
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_75,c_77])).

tff(c_12,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [C_14,A_12,B_13] :
      ( k6_subset_1(k7_relat_1(C_14,A_12),k7_relat_1(C_14,B_13)) = k7_relat_1(C_14,k6_subset_1(A_12,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_196,plain,(
    ! [C_56,A_57,B_58] :
      ( k4_xboole_0(k7_relat_1(C_56,A_57),k7_relat_1(C_56,B_58)) = k7_relat_1(C_56,k4_xboole_0(A_57,B_58))
      | ~ v1_relat_1(C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_18])).

tff(c_712,plain,(
    ! [B_116,B_117] :
      ( k7_relat_1(B_116,k4_xboole_0(k1_relat_1(B_116),B_117)) = k4_xboole_0(B_116,k7_relat_1(B_116,B_117))
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_196])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_17,A_15),B_16) = k1_xboole_0
      | ~ r1_xboole_0(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50645,plain,(
    ! [B_1318,B_1319,B_1320] :
      ( k7_relat_1(k4_xboole_0(B_1318,k7_relat_1(B_1318,B_1319)),B_1320) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(B_1318),B_1319),B_1320)
      | ~ v1_relat_1(B_1318)
      | ~ v1_relat_1(B_1318)
      | ~ v1_relat_1(B_1318) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_20])).

tff(c_50746,plain,(
    ! [B_1321,B_1322,A_1323] :
      ( k7_relat_1(k4_xboole_0(B_1321,k7_relat_1(B_1321,B_1322)),A_1323) = k1_xboole_0
      | ~ v1_relat_1(B_1321)
      | ~ r1_tarski(A_1323,B_1322) ) ),
    inference(resolution,[status(thm)],[c_46,c_50645])).

tff(c_24,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24])).

tff(c_51871,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50746,c_29])).

tff(c_52084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_51871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.85/17.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.85/17.23  
% 26.85/17.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.85/17.23  %$ v4_relat_1 > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 26.85/17.23  
% 26.85/17.23  %Foreground sorts:
% 26.85/17.23  
% 26.85/17.23  
% 26.85/17.23  %Background operators:
% 26.85/17.23  
% 26.85/17.23  
% 26.85/17.23  %Foreground operators:
% 26.85/17.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.85/17.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.85/17.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 26.85/17.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.85/17.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.85/17.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.85/17.23  tff('#skF_2', type, '#skF_2': $i).
% 26.85/17.23  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 26.85/17.23  tff('#skF_3', type, '#skF_3': $i).
% 26.85/17.23  tff('#skF_1', type, '#skF_1': $i).
% 26.85/17.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.85/17.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 26.85/17.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.85/17.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 26.85/17.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 26.85/17.23  
% 26.85/17.24  tff(f_70, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 26.85/17.24  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 26.85/17.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 26.85/17.24  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 26.85/17.24  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 26.85/17.24  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 26.85/17.24  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 26.85/17.24  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 26.85/17.24  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 26.85/17.24  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 26.85/17.24  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 26.85/17.24  tff(c_43, plain, (![A_25, C_26, B_27]: (r1_xboole_0(A_25, k4_xboole_0(C_26, B_27)) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 26.85/17.24  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 26.85/17.24  tff(c_46, plain, (![C_26, B_27, A_25]: (r1_xboole_0(k4_xboole_0(C_26, B_27), A_25) | ~r1_tarski(A_25, B_27))), inference(resolution, [status(thm)], [c_43, c_2])).
% 26.85/17.24  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 26.85/17.24  tff(c_66, plain, (![B_35, A_36]: (v4_relat_1(B_35, A_36) | ~r1_tarski(k1_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 26.85/17.24  tff(c_75, plain, (![B_35]: (v4_relat_1(B_35, k1_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_8, c_66])).
% 26.85/17.24  tff(c_77, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=B_38 | ~v4_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 26.85/17.24  tff(c_81, plain, (![B_35]: (k7_relat_1(B_35, k1_relat_1(B_35))=B_35 | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_75, c_77])).
% 26.85/17.24  tff(c_12, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.85/17.24  tff(c_18, plain, (![C_14, A_12, B_13]: (k6_subset_1(k7_relat_1(C_14, A_12), k7_relat_1(C_14, B_13))=k7_relat_1(C_14, k6_subset_1(A_12, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 26.85/17.24  tff(c_196, plain, (![C_56, A_57, B_58]: (k4_xboole_0(k7_relat_1(C_56, A_57), k7_relat_1(C_56, B_58))=k7_relat_1(C_56, k4_xboole_0(A_57, B_58)) | ~v1_relat_1(C_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_18])).
% 26.85/17.24  tff(c_712, plain, (![B_116, B_117]: (k7_relat_1(B_116, k4_xboole_0(k1_relat_1(B_116), B_117))=k4_xboole_0(B_116, k7_relat_1(B_116, B_117)) | ~v1_relat_1(B_116) | ~v1_relat_1(B_116))), inference(superposition, [status(thm), theory('equality')], [c_81, c_196])).
% 26.85/17.24  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k1_xboole_0 | ~r1_xboole_0(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 26.85/17.24  tff(c_50645, plain, (![B_1318, B_1319, B_1320]: (k7_relat_1(k4_xboole_0(B_1318, k7_relat_1(B_1318, B_1319)), B_1320)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(B_1318), B_1319), B_1320) | ~v1_relat_1(B_1318) | ~v1_relat_1(B_1318) | ~v1_relat_1(B_1318))), inference(superposition, [status(thm), theory('equality')], [c_712, c_20])).
% 26.85/17.24  tff(c_50746, plain, (![B_1321, B_1322, A_1323]: (k7_relat_1(k4_xboole_0(B_1321, k7_relat_1(B_1321, B_1322)), A_1323)=k1_xboole_0 | ~v1_relat_1(B_1321) | ~r1_tarski(A_1323, B_1322))), inference(resolution, [status(thm)], [c_46, c_50645])).
% 26.85/17.24  tff(c_24, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 26.85/17.24  tff(c_29, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24])).
% 26.85/17.24  tff(c_51871, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50746, c_29])).
% 26.85/17.24  tff(c_52084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_51871])).
% 26.85/17.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.85/17.24  
% 26.85/17.24  Inference rules
% 26.85/17.24  ----------------------
% 26.85/17.24  #Ref     : 0
% 26.85/17.24  #Sup     : 16442
% 26.85/17.24  #Fact    : 0
% 26.85/17.24  #Define  : 0
% 26.85/17.24  #Split   : 45
% 26.85/17.24  #Chain   : 0
% 26.85/17.24  #Close   : 0
% 26.85/17.24  
% 26.85/17.24  Ordering : KBO
% 26.85/17.24  
% 26.85/17.24  Simplification rules
% 26.85/17.24  ----------------------
% 26.85/17.24  #Subsume      : 5320
% 26.85/17.24  #Demod        : 489
% 26.85/17.24  #Tautology    : 368
% 26.85/17.24  #SimpNegUnit  : 0
% 26.85/17.24  #BackRed      : 0
% 26.85/17.24  
% 26.85/17.24  #Partial instantiations: 0
% 26.85/17.24  #Strategies tried      : 1
% 26.85/17.24  
% 26.85/17.24  Timing (in seconds)
% 26.85/17.24  ----------------------
% 26.85/17.25  Preprocessing        : 0.32
% 26.85/17.25  Parsing              : 0.17
% 26.85/17.25  CNF conversion       : 0.02
% 26.85/17.25  Main loop            : 16.11
% 26.85/17.25  Inferencing          : 2.22
% 26.85/17.25  Reduction            : 2.13
% 26.85/17.25  Demodulation         : 1.47
% 26.85/17.25  BG Simplification    : 0.33
% 26.85/17.25  Subsumption          : 10.77
% 26.85/17.25  Abstraction          : 0.41
% 26.85/17.25  MUC search           : 0.00
% 26.85/17.25  Cooper               : 0.00
% 26.85/17.25  Total                : 16.46
% 26.85/17.25  Index Insertion      : 0.00
% 26.85/17.25  Index Deletion       : 0.00
% 26.85/17.25  Index Matching       : 0.00
% 26.85/17.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
