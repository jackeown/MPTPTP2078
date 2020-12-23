%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  69 expanded)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

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
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_7,A_6] : r1_xboole_0(B_7,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

tff(c_43,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_xboole_0(A_26,C_27)
      | ~ r1_xboole_0(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_35,A_36,B_37] :
      ( r1_xboole_0(A_35,k4_xboole_0(A_36,B_37))
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(resolution,[status(thm)],[c_37,c_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_36,B_37,A_35] :
      ( r1_xboole_0(k4_xboole_0(A_36,B_37),A_35)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(A_8,k1_zfmisc_1(k3_tarski(A_8))) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(C_16,k6_subset_1(A_14,B_15)) = k6_subset_1(C_16,k7_relat_1(C_16,B_15))
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,(
    ! [C_47,A_48,B_49] :
      ( k7_relat_1(C_47,k4_xboole_0(A_48,B_49)) = k4_xboole_0(C_47,k7_relat_1(C_47,B_49))
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_149,plain,(
    ! [C_75,B_76] :
      ( k7_relat_1(C_75,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_75))),B_76)) = k4_xboole_0(C_75,k7_relat_1(C_75,B_76))
      | ~ v1_relat_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_8,c_94])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_13,A_11),B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_309,plain,(
    ! [C_137,B_138,B_139] :
      ( k7_relat_1(k4_xboole_0(C_137,k7_relat_1(C_137,B_138)),B_139) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_137))),B_138),B_139)
      | ~ v1_relat_1(C_137)
      | ~ v1_relat_1(C_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_12])).

tff(c_402,plain,(
    ! [C_142,B_143,A_144] :
      ( k7_relat_1(k4_xboole_0(C_142,k7_relat_1(C_142,B_143)),A_144) = k1_xboole_0
      | ~ v1_relat_1(C_142)
      | ~ r1_tarski(A_144,B_143) ) ),
    inference(resolution,[status(thm)],[c_72,c_309])).

tff(c_16,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_429,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_21])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.90  
% 3.32/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.91  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.32/1.91  
% 3.32/1.91  %Foreground sorts:
% 3.32/1.91  
% 3.32/1.91  
% 3.32/1.91  %Background operators:
% 3.32/1.91  
% 3.32/1.91  
% 3.32/1.91  %Foreground operators:
% 3.32/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.91  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.32/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.91  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.91  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.32/1.91  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.91  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.32/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.91  
% 3.65/1.93  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 3.65/1.93  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.65/1.93  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.65/1.93  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.65/1.93  tff(f_39, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 3.65/1.93  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.65/1.93  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 3.65/1.93  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 3.65/1.93  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.65/1.93  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.65/1.93  tff(c_6, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.65/1.93  tff(c_34, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.93  tff(c_37, plain, (![B_7, A_6]: (r1_xboole_0(B_7, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_6, c_34])).
% 3.65/1.93  tff(c_43, plain, (![A_26, C_27, B_28]: (r1_xboole_0(A_26, C_27) | ~r1_xboole_0(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.93  tff(c_66, plain, (![A_35, A_36, B_37]: (r1_xboole_0(A_35, k4_xboole_0(A_36, B_37)) | ~r1_tarski(A_35, B_37))), inference(resolution, [status(thm)], [c_37, c_43])).
% 3.65/1.93  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.93  tff(c_72, plain, (![A_36, B_37, A_35]: (r1_xboole_0(k4_xboole_0(A_36, B_37), A_35) | ~r1_tarski(A_35, B_37))), inference(resolution, [status(thm)], [c_66, c_2])).
% 3.65/1.93  tff(c_8, plain, (![A_8]: (r1_tarski(A_8, k1_zfmisc_1(k3_tarski(A_8))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.65/1.93  tff(c_10, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.93  tff(c_14, plain, (![C_16, A_14, B_15]: (k7_relat_1(C_16, k6_subset_1(A_14, B_15))=k6_subset_1(C_16, k7_relat_1(C_16, B_15)) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.65/1.93  tff(c_94, plain, (![C_47, A_48, B_49]: (k7_relat_1(C_47, k4_xboole_0(A_48, B_49))=k4_xboole_0(C_47, k7_relat_1(C_47, B_49)) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 3.65/1.93  tff(c_149, plain, (![C_75, B_76]: (k7_relat_1(C_75, k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_75))), B_76))=k4_xboole_0(C_75, k7_relat_1(C_75, B_76)) | ~v1_relat_1(C_75))), inference(resolution, [status(thm)], [c_8, c_94])).
% 3.65/1.93  tff(c_12, plain, (![C_13, A_11, B_12]: (k7_relat_1(k7_relat_1(C_13, A_11), B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.93  tff(c_309, plain, (![C_137, B_138, B_139]: (k7_relat_1(k4_xboole_0(C_137, k7_relat_1(C_137, B_138)), B_139)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_137))), B_138), B_139) | ~v1_relat_1(C_137) | ~v1_relat_1(C_137))), inference(superposition, [status(thm), theory('equality')], [c_149, c_12])).
% 3.65/1.93  tff(c_402, plain, (![C_142, B_143, A_144]: (k7_relat_1(k4_xboole_0(C_142, k7_relat_1(C_142, B_143)), A_144)=k1_xboole_0 | ~v1_relat_1(C_142) | ~r1_tarski(A_144, B_143))), inference(resolution, [status(thm)], [c_72, c_309])).
% 3.65/1.93  tff(c_16, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.65/1.93  tff(c_21, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 3.65/1.93  tff(c_429, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_402, c_21])).
% 3.65/1.93  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_429])).
% 3.65/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.93  
% 3.65/1.93  Inference rules
% 3.65/1.93  ----------------------
% 3.65/1.93  #Ref     : 0
% 3.65/1.93  #Sup     : 120
% 3.65/1.93  #Fact    : 0
% 3.65/1.93  #Define  : 0
% 3.65/1.93  #Split   : 0
% 3.65/1.93  #Chain   : 0
% 3.65/1.93  #Close   : 0
% 3.65/1.93  
% 3.65/1.93  Ordering : KBO
% 3.65/1.93  
% 3.65/1.93  Simplification rules
% 3.65/1.93  ----------------------
% 3.65/1.93  #Subsume      : 9
% 3.65/1.93  #Demod        : 7
% 3.65/1.93  #Tautology    : 12
% 3.65/1.93  #SimpNegUnit  : 0
% 3.65/1.93  #BackRed      : 0
% 3.65/1.93  
% 3.65/1.93  #Partial instantiations: 0
% 3.65/1.93  #Strategies tried      : 1
% 3.65/1.93  
% 3.65/1.93  Timing (in seconds)
% 3.65/1.93  ----------------------
% 3.65/1.93  Preprocessing        : 0.45
% 3.65/1.93  Parsing              : 0.24
% 3.65/1.93  CNF conversion       : 0.03
% 3.65/1.93  Main loop            : 0.53
% 3.65/1.93  Inferencing          : 0.19
% 3.65/1.93  Reduction            : 0.15
% 3.65/1.93  Demodulation         : 0.09
% 3.65/1.94  BG Simplification    : 0.03
% 3.65/1.94  Subsumption          : 0.13
% 3.65/1.94  Abstraction          : 0.03
% 3.65/1.94  MUC search           : 0.00
% 3.65/1.94  Cooper               : 0.00
% 3.65/1.94  Total                : 1.03
% 3.65/1.94  Index Insertion      : 0.00
% 3.65/1.94  Index Deletion       : 0.00
% 3.65/1.94  Index Matching       : 0.00
% 3.65/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
