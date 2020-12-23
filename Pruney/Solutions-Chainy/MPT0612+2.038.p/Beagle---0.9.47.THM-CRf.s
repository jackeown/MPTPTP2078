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
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  58 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_33,axiom,(
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
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_xboole_0(A_20,k4_xboole_0(C_21,B_22))
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [C_21,B_22,A_20] :
      ( r1_xboole_0(k4_xboole_0(C_21,B_22),A_20)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(A_6,k1_zfmisc_1(k3_tarski(A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(C_14,k6_subset_1(A_12,B_13)) = k6_subset_1(C_14,k7_relat_1(C_14,B_13))
      | ~ r1_tarski(k1_relat_1(C_14),A_12)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [C_29,A_30,B_31] :
      ( k7_relat_1(C_29,k4_xboole_0(A_30,B_31)) = k4_xboole_0(C_29,k7_relat_1(C_29,B_31))
      | ~ r1_tarski(k1_relat_1(C_29),A_30)
      | ~ v1_relat_1(C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_60,plain,(
    ! [C_32,B_33] :
      ( k7_relat_1(C_32,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_32))),B_33)) = k4_xboole_0(C_32,k7_relat_1(C_32,B_33))
      | ~ v1_relat_1(C_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( k7_relat_1(k7_relat_1(C_11,A_9),B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [C_48,B_49,B_50] :
      ( k7_relat_1(k4_xboole_0(C_48,k7_relat_1(C_48,B_49)),B_50) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_48))),B_49),B_50)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10])).

tff(c_106,plain,(
    ! [C_51,B_52,A_53] :
      ( k7_relat_1(k4_xboole_0(C_51,k7_relat_1(C_51,B_52)),A_53) = k1_xboole_0
      | ~ v1_relat_1(C_51)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_35,c_97])).

tff(c_14,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_126,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_19])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.88/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.88/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.17  
% 1.88/1.18  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 1.88/1.18  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.88/1.18  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.88/1.18  tff(f_35, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 1.88/1.18  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.88/1.18  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 1.88/1.18  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.88/1.18  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.18  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.18  tff(c_32, plain, (![A_20, C_21, B_22]: (r1_xboole_0(A_20, k4_xboole_0(C_21, B_22)) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.18  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.18  tff(c_35, plain, (![C_21, B_22, A_20]: (r1_xboole_0(k4_xboole_0(C_21, B_22), A_20) | ~r1_tarski(A_20, B_22))), inference(resolution, [status(thm)], [c_32, c_2])).
% 1.88/1.18  tff(c_6, plain, (![A_6]: (r1_tarski(A_6, k1_zfmisc_1(k3_tarski(A_6))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.18  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.18  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(C_14, k6_subset_1(A_12, B_13))=k6_subset_1(C_14, k7_relat_1(C_14, B_13)) | ~r1_tarski(k1_relat_1(C_14), A_12) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.88/1.18  tff(c_55, plain, (![C_29, A_30, B_31]: (k7_relat_1(C_29, k4_xboole_0(A_30, B_31))=k4_xboole_0(C_29, k7_relat_1(C_29, B_31)) | ~r1_tarski(k1_relat_1(C_29), A_30) | ~v1_relat_1(C_29))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_12])).
% 1.88/1.18  tff(c_60, plain, (![C_32, B_33]: (k7_relat_1(C_32, k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_32))), B_33))=k4_xboole_0(C_32, k7_relat_1(C_32, B_33)) | ~v1_relat_1(C_32))), inference(resolution, [status(thm)], [c_6, c_55])).
% 1.88/1.18  tff(c_10, plain, (![C_11, A_9, B_10]: (k7_relat_1(k7_relat_1(C_11, A_9), B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.18  tff(c_97, plain, (![C_48, B_49, B_50]: (k7_relat_1(k4_xboole_0(C_48, k7_relat_1(C_48, B_49)), B_50)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_48))), B_49), B_50) | ~v1_relat_1(C_48) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_60, c_10])).
% 1.88/1.18  tff(c_106, plain, (![C_51, B_52, A_53]: (k7_relat_1(k4_xboole_0(C_51, k7_relat_1(C_51, B_52)), A_53)=k1_xboole_0 | ~v1_relat_1(C_51) | ~r1_tarski(A_53, B_52))), inference(resolution, [status(thm)], [c_35, c_97])).
% 1.88/1.18  tff(c_14, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.18  tff(c_19, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 1.88/1.18  tff(c_126, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_19])).
% 1.88/1.18  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_126])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 34
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 0
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 2
% 1.88/1.18  #Demod        : 5
% 1.88/1.18  #Tautology    : 7
% 1.88/1.18  #SimpNegUnit  : 0
% 1.88/1.18  #BackRed      : 0
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.18  Preprocessing        : 0.28
% 1.88/1.18  Parsing              : 0.15
% 1.88/1.18  CNF conversion       : 0.02
% 1.88/1.18  Main loop            : 0.15
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.03
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.45
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
