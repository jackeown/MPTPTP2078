%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  69 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

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

tff(c_6,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_7,A_6] : r1_xboole_0(B_7,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

tff(c_43,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_xboole_0(A_28,C_29)
      | ~ r1_xboole_0(B_30,C_29)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_37,A_38,B_39] :
      ( r1_xboole_0(A_37,k4_xboole_0(A_38,B_39))
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(resolution,[status(thm)],[c_37,c_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_38,B_39,A_37] :
      ( r1_xboole_0(k4_xboole_0(A_38,B_39),A_37)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,(
    ! [C_49,A_50,B_51] :
      ( k7_relat_1(C_49,k4_xboole_0(A_50,B_51)) = k4_xboole_0(C_49,k7_relat_1(C_49,B_51))
      | ~ r1_tarski(k1_relat_1(C_49),A_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_149,plain,(
    ! [C_84,B_85,B_86] :
      ( k7_relat_1(C_84,k4_xboole_0(k2_xboole_0(k1_relat_1(C_84),B_85),B_86)) = k4_xboole_0(C_84,k7_relat_1(C_84,B_86))
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_8,c_94])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_308,plain,(
    ! [C_174,B_175,B_176,B_177] :
      ( k7_relat_1(k4_xboole_0(C_174,k7_relat_1(C_174,B_175)),B_176) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_174),B_177),B_175),B_176)
      | ~ v1_relat_1(C_174)
      | ~ v1_relat_1(C_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_12])).

tff(c_401,plain,(
    ! [C_180,B_181,A_182] :
      ( k7_relat_1(k4_xboole_0(C_180,k7_relat_1(C_180,B_181)),A_182) = k1_xboole_0
      | ~ v1_relat_1(C_180)
      | ~ r1_tarski(A_182,B_181) ) ),
    inference(resolution,[status(thm)],[c_72,c_308])).

tff(c_16,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_428,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_21])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.42  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.42  
% 2.49/1.42  %Foreground sorts:
% 2.49/1.42  
% 2.49/1.42  
% 2.49/1.42  %Background operators:
% 2.49/1.42  
% 2.49/1.42  
% 2.49/1.42  %Foreground operators:
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.49/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.42  
% 2.49/1.43  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 2.49/1.43  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.49/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.49/1.43  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.49/1.43  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.49/1.43  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.49/1.43  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.49/1.43  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.49/1.43  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.43  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.43  tff(c_6, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.43  tff(c_34, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.43  tff(c_37, plain, (![B_7, A_6]: (r1_xboole_0(B_7, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_6, c_34])).
% 2.49/1.43  tff(c_43, plain, (![A_28, C_29, B_30]: (r1_xboole_0(A_28, C_29) | ~r1_xboole_0(B_30, C_29) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.43  tff(c_66, plain, (![A_37, A_38, B_39]: (r1_xboole_0(A_37, k4_xboole_0(A_38, B_39)) | ~r1_tarski(A_37, B_39))), inference(resolution, [status(thm)], [c_37, c_43])).
% 2.49/1.43  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.43  tff(c_72, plain, (![A_38, B_39, A_37]: (r1_xboole_0(k4_xboole_0(A_38, B_39), A_37) | ~r1_tarski(A_37, B_39))), inference(resolution, [status(thm)], [c_66, c_2])).
% 2.49/1.43  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.49/1.43  tff(c_10, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.43  tff(c_14, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.43  tff(c_94, plain, (![C_49, A_50, B_51]: (k7_relat_1(C_49, k4_xboole_0(A_50, B_51))=k4_xboole_0(C_49, k7_relat_1(C_49, B_51)) | ~r1_tarski(k1_relat_1(C_49), A_50) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 2.49/1.43  tff(c_149, plain, (![C_84, B_85, B_86]: (k7_relat_1(C_84, k4_xboole_0(k2_xboole_0(k1_relat_1(C_84), B_85), B_86))=k4_xboole_0(C_84, k7_relat_1(C_84, B_86)) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_8, c_94])).
% 2.49/1.43  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.43  tff(c_308, plain, (![C_174, B_175, B_176, B_177]: (k7_relat_1(k4_xboole_0(C_174, k7_relat_1(C_174, B_175)), B_176)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_174), B_177), B_175), B_176) | ~v1_relat_1(C_174) | ~v1_relat_1(C_174))), inference(superposition, [status(thm), theory('equality')], [c_149, c_12])).
% 2.49/1.43  tff(c_401, plain, (![C_180, B_181, A_182]: (k7_relat_1(k4_xboole_0(C_180, k7_relat_1(C_180, B_181)), A_182)=k1_xboole_0 | ~v1_relat_1(C_180) | ~r1_tarski(A_182, B_181))), inference(resolution, [status(thm)], [c_72, c_308])).
% 2.49/1.43  tff(c_16, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.43  tff(c_21, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 2.49/1.43  tff(c_428, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_401, c_21])).
% 2.49/1.43  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_428])).
% 2.49/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.43  
% 2.49/1.43  Inference rules
% 2.49/1.43  ----------------------
% 2.49/1.43  #Ref     : 0
% 2.49/1.43  #Sup     : 119
% 2.49/1.43  #Fact    : 0
% 2.49/1.43  #Define  : 0
% 2.49/1.43  #Split   : 0
% 2.49/1.43  #Chain   : 0
% 2.49/1.43  #Close   : 0
% 2.49/1.43  
% 2.49/1.43  Ordering : KBO
% 2.49/1.43  
% 2.49/1.43  Simplification rules
% 2.49/1.43  ----------------------
% 2.49/1.43  #Subsume      : 8
% 2.49/1.43  #Demod        : 8
% 2.49/1.43  #Tautology    : 13
% 2.49/1.43  #SimpNegUnit  : 0
% 2.49/1.43  #BackRed      : 0
% 2.49/1.43  
% 2.49/1.43  #Partial instantiations: 0
% 2.49/1.43  #Strategies tried      : 1
% 2.49/1.43  
% 2.49/1.43  Timing (in seconds)
% 2.49/1.43  ----------------------
% 2.85/1.44  Preprocessing        : 0.30
% 2.85/1.44  Parsing              : 0.16
% 2.85/1.44  CNF conversion       : 0.02
% 2.85/1.44  Main loop            : 0.31
% 2.85/1.44  Inferencing          : 0.12
% 2.85/1.44  Reduction            : 0.08
% 2.85/1.44  Demodulation         : 0.06
% 2.85/1.44  BG Simplification    : 0.01
% 2.85/1.44  Subsumption          : 0.08
% 2.85/1.44  Abstraction          : 0.02
% 2.85/1.44  MUC search           : 0.00
% 2.85/1.44  Cooper               : 0.00
% 2.85/1.44  Total                : 0.64
% 2.85/1.44  Index Insertion      : 0.00
% 2.85/1.44  Index Deletion       : 0.00
% 2.85/1.44  Index Matching       : 0.00
% 2.85/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
