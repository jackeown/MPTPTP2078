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
% DateTime   : Thu Dec  3 10:02:44 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   45 (  58 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  87 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_43,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,k4_xboole_0(C_28,B_29))
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [A_36,C_37,B_38] :
      ( k4_xboole_0(A_36,k4_xboole_0(C_37,B_38)) = A_36
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(resolution,[status(thm)],[c_43,c_8])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,k4_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_101,plain,(
    ! [A_45,A_46,C_47,B_48] :
      ( r1_xboole_0(A_45,A_46)
      | ~ r1_tarski(A_45,k4_xboole_0(C_47,B_48))
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_12])).

tff(c_107,plain,(
    ! [C_47,B_48,A_46] :
      ( r1_xboole_0(k4_xboole_0(C_47,B_48),A_46)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(resolution,[status(thm)],[c_53,c_101])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [C_18,A_16,B_17] :
      ( k7_relat_1(C_18,k6_subset_1(A_16,B_17)) = k6_subset_1(C_18,k7_relat_1(C_18,B_17))
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_108,plain,(
    ! [C_49,A_50,B_51] :
      ( k7_relat_1(C_49,k4_xboole_0(A_50,B_51)) = k4_xboole_0(C_49,k7_relat_1(C_49,B_51))
      | ~ r1_tarski(k1_relat_1(C_49),A_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_490,plain,(
    ! [C_124,B_125] :
      ( k7_relat_1(C_124,k4_xboole_0(k1_relat_1(C_124),B_125)) = k4_xboole_0(C_124,k7_relat_1(C_124,B_125))
      | ~ v1_relat_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_53,c_108])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1021,plain,(
    ! [C_236,B_237,B_238] :
      ( k7_relat_1(k4_xboole_0(C_236,k7_relat_1(C_236,B_237)),B_238) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(C_236),B_237),B_238)
      | ~ v1_relat_1(C_236)
      | ~ v1_relat_1(C_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_16])).

tff(c_1055,plain,(
    ! [C_239,B_240,A_241] :
      ( k7_relat_1(k4_xboole_0(C_239,k7_relat_1(C_239,B_240)),A_241) = k1_xboole_0
      | ~ v1_relat_1(C_239)
      | ~ r1_tarski(A_241,B_240) ) ),
    inference(resolution,[status(thm)],[c_107,c_1021])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_25,plain,(
    k7_relat_1(k4_xboole_0('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_1084,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_25])).

tff(c_1112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_1084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.64  
% 3.39/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.39/1.64  
% 3.39/1.64  %Foreground sorts:
% 3.39/1.64  
% 3.39/1.64  
% 3.39/1.64  %Background operators:
% 3.39/1.64  
% 3.39/1.64  
% 3.39/1.64  %Foreground operators:
% 3.39/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.39/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.39/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.64  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.39/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.64  
% 3.39/1.65  tff(f_61, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 3.39/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.39/1.65  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.39/1.65  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.39/1.65  tff(f_42, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.39/1.65  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 3.39/1.65  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 3.39/1.65  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.65  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.65  tff(c_48, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.65  tff(c_53, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_48, c_4])).
% 3.39/1.65  tff(c_43, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, k4_xboole_0(C_28, B_29)) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.65  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.65  tff(c_59, plain, (![A_36, C_37, B_38]: (k4_xboole_0(A_36, k4_xboole_0(C_37, B_38))=A_36 | ~r1_tarski(A_36, B_38))), inference(resolution, [status(thm)], [c_43, c_8])).
% 3.39/1.65  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, k4_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.65  tff(c_101, plain, (![A_45, A_46, C_47, B_48]: (r1_xboole_0(A_45, A_46) | ~r1_tarski(A_45, k4_xboole_0(C_47, B_48)) | ~r1_tarski(A_46, B_48))), inference(superposition, [status(thm), theory('equality')], [c_59, c_12])).
% 3.39/1.65  tff(c_107, plain, (![C_47, B_48, A_46]: (r1_xboole_0(k4_xboole_0(C_47, B_48), A_46) | ~r1_tarski(A_46, B_48))), inference(resolution, [status(thm)], [c_53, c_101])).
% 3.39/1.65  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.65  tff(c_18, plain, (![C_18, A_16, B_17]: (k7_relat_1(C_18, k6_subset_1(A_16, B_17))=k6_subset_1(C_18, k7_relat_1(C_18, B_17)) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.65  tff(c_108, plain, (![C_49, A_50, B_51]: (k7_relat_1(C_49, k4_xboole_0(A_50, B_51))=k4_xboole_0(C_49, k7_relat_1(C_49, B_51)) | ~r1_tarski(k1_relat_1(C_49), A_50) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 3.39/1.65  tff(c_490, plain, (![C_124, B_125]: (k7_relat_1(C_124, k4_xboole_0(k1_relat_1(C_124), B_125))=k4_xboole_0(C_124, k7_relat_1(C_124, B_125)) | ~v1_relat_1(C_124))), inference(resolution, [status(thm)], [c_53, c_108])).
% 3.39/1.65  tff(c_16, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.39/1.65  tff(c_1021, plain, (![C_236, B_237, B_238]: (k7_relat_1(k4_xboole_0(C_236, k7_relat_1(C_236, B_237)), B_238)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(C_236), B_237), B_238) | ~v1_relat_1(C_236) | ~v1_relat_1(C_236))), inference(superposition, [status(thm), theory('equality')], [c_490, c_16])).
% 3.39/1.65  tff(c_1055, plain, (![C_239, B_240, A_241]: (k7_relat_1(k4_xboole_0(C_239, k7_relat_1(C_239, B_240)), A_241)=k1_xboole_0 | ~v1_relat_1(C_239) | ~r1_tarski(A_241, B_240))), inference(resolution, [status(thm)], [c_107, c_1021])).
% 3.39/1.65  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.65  tff(c_25, plain, (k7_relat_1(k4_xboole_0('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 3.39/1.65  tff(c_1084, plain, (~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1055, c_25])).
% 3.39/1.65  tff(c_1112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_1084])).
% 3.39/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.65  
% 3.39/1.65  Inference rules
% 3.39/1.65  ----------------------
% 3.39/1.65  #Ref     : 0
% 3.39/1.65  #Sup     : 334
% 3.39/1.65  #Fact    : 0
% 3.39/1.65  #Define  : 0
% 3.39/1.65  #Split   : 4
% 3.39/1.65  #Chain   : 0
% 3.39/1.65  #Close   : 0
% 3.39/1.65  
% 3.39/1.65  Ordering : KBO
% 3.39/1.65  
% 3.39/1.65  Simplification rules
% 3.39/1.65  ----------------------
% 3.39/1.65  #Subsume      : 105
% 3.39/1.65  #Demod        : 8
% 3.39/1.65  #Tautology    : 36
% 3.39/1.65  #SimpNegUnit  : 0
% 3.39/1.65  #BackRed      : 0
% 3.39/1.65  
% 3.39/1.65  #Partial instantiations: 0
% 3.39/1.65  #Strategies tried      : 1
% 3.39/1.65  
% 3.39/1.65  Timing (in seconds)
% 3.39/1.65  ----------------------
% 3.39/1.66  Preprocessing        : 0.31
% 3.39/1.66  Parsing              : 0.17
% 3.39/1.66  CNF conversion       : 0.02
% 3.39/1.66  Main loop            : 0.53
% 3.39/1.66  Inferencing          : 0.18
% 3.39/1.66  Reduction            : 0.12
% 3.39/1.66  Demodulation         : 0.08
% 3.39/1.66  BG Simplification    : 0.02
% 3.39/1.66  Subsumption          : 0.18
% 3.39/1.66  Abstraction          : 0.02
% 3.39/1.66  MUC search           : 0.00
% 3.39/1.66  Cooper               : 0.00
% 3.39/1.66  Total                : 0.87
% 3.39/1.66  Index Insertion      : 0.00
% 3.39/1.66  Index Deletion       : 0.00
% 3.39/1.66  Index Matching       : 0.00
% 3.39/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
