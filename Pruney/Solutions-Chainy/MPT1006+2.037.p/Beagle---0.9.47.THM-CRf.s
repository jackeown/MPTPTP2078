%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:07 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 102 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 ( 146 expanded)
%              Number of equality atoms :   39 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_243,plain,(
    ! [A_52,B_53,D_54,C_55] :
      ( r1_tarski(k8_relset_1(A_52,B_53,D_54,C_55),A_52)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(D_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_245,plain,(
    ! [C_55] :
      ( r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_55),k1_xboole_0)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_243])).

tff(c_332,plain,(
    ! [C_60] : r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_60),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_245])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_336,plain,(
    ! [C_60] : k3_xboole_0(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_60),k1_xboole_0) = k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_60) ),
    inference(resolution,[status(thm)],[c_332,c_10])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_43,B_44,C_45] :
      ( k3_xboole_0(A_43,k2_xboole_0(B_44,C_45)) = k3_xboole_0(A_43,C_45)
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [B_46,C_47] :
      ( k3_xboole_0(B_46,C_47) = B_46
      | ~ r1_xboole_0(B_46,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_161,plain,(
    ! [B_2,C_47] :
      ( k3_xboole_0(B_2,C_47) = B_2
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_166,plain,(
    ! [B_48,C_49] :
      ( k3_xboole_0(B_48,C_49) = B_48
      | k1_xboole_0 != B_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_82,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),C_40) = k3_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_3,C_40] : k3_xboole_0(A_3,k4_xboole_0(A_3,C_40)) = k4_xboole_0(A_3,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_211,plain,(
    ! [B_50,C_51] :
      ( k4_xboole_0(B_50,C_51) = B_50
      | k1_xboole_0 != B_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_104])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = k1_xboole_0
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_250,plain,(
    ! [B_56,C_57] :
      ( k3_xboole_0(B_56,C_57) = k1_xboole_0
      | k1_xboole_0 != B_56 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_56])).

tff(c_298,plain,(
    ! [B_58,C_59] :
      ( k4_xboole_0(B_58,C_59) = k1_xboole_0
      | k1_xboole_0 != B_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_104])).

tff(c_353,plain,(
    ! [C_59] : k4_xboole_0(k1_xboole_0,C_59) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_104])).

tff(c_441,plain,(
    ! [C_68] : k3_xboole_0(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_68),k1_xboole_0) = k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_68) ),
    inference(resolution,[status(thm)],[c_332,c_10])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k3_xboole_0(A_9,B_10),C_11) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_453,plain,(
    ! [C_68,C_11] : k3_xboole_0(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_68),k4_xboole_0(k1_xboole_0,C_11)) = k4_xboole_0(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_68),C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_12])).

tff(c_911,plain,(
    ! [C_91,C_92] : k4_xboole_0(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_91),C_92) = k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_6,c_353,c_453])).

tff(c_982,plain,(
    ! [C_91,C_92] : k3_xboole_0(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_91),C_92) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_56])).

tff(c_988,plain,(
    ! [C_60] : k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_336])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.40  
% 2.66/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.40  %$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.40  
% 2.66/1.40  %Foreground sorts:
% 2.66/1.40  
% 2.66/1.40  
% 2.66/1.40  %Background operators:
% 2.66/1.40  
% 2.66/1.40  
% 2.66/1.40  %Foreground operators:
% 2.66/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.66/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.40  
% 2.66/1.42  tff(f_62, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.66/1.42  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 2.66/1.42  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.66/1.42  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.66/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.66/1.42  tff(f_43, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.66/1.42  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.66/1.42  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.66/1.42  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.66/1.42  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.42  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.42  tff(c_243, plain, (![A_52, B_53, D_54, C_55]: (r1_tarski(k8_relset_1(A_52, B_53, D_54, C_55), A_52) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(D_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.42  tff(c_245, plain, (![C_55]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_55), k1_xboole_0) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_243])).
% 2.66/1.42  tff(c_332, plain, (![C_60]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_60), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_245])).
% 2.66/1.42  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.42  tff(c_336, plain, (![C_60]: (k3_xboole_0(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_60), k1_xboole_0)=k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_60))), inference(resolution, [status(thm)], [c_332, c_10])).
% 2.66/1.42  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.42  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.42  tff(c_127, plain, (![A_43, B_44, C_45]: (k3_xboole_0(A_43, k2_xboole_0(B_44, C_45))=k3_xboole_0(A_43, C_45) | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.42  tff(c_8, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.42  tff(c_155, plain, (![B_46, C_47]: (k3_xboole_0(B_46, C_47)=B_46 | ~r1_xboole_0(B_46, B_46))), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 2.66/1.42  tff(c_161, plain, (![B_2, C_47]: (k3_xboole_0(B_2, C_47)=B_2 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_155])).
% 2.66/1.42  tff(c_166, plain, (![B_48, C_49]: (k3_xboole_0(B_48, C_49)=B_48 | k1_xboole_0!=B_48)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_161])).
% 2.66/1.42  tff(c_82, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), C_40)=k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.42  tff(c_104, plain, (![A_3, C_40]: (k3_xboole_0(A_3, k4_xboole_0(A_3, C_40))=k4_xboole_0(A_3, C_40))), inference(superposition, [status(thm), theory('equality')], [c_6, c_82])).
% 2.66/1.42  tff(c_211, plain, (![B_50, C_51]: (k4_xboole_0(B_50, C_51)=B_50 | k1_xboole_0!=B_50)), inference(superposition, [status(thm), theory('equality')], [c_166, c_104])).
% 2.66/1.42  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.42  tff(c_49, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.42  tff(c_56, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=k1_xboole_0 | k4_xboole_0(A_15, B_16)!=A_15)), inference(resolution, [status(thm)], [c_18, c_49])).
% 2.66/1.42  tff(c_250, plain, (![B_56, C_57]: (k3_xboole_0(B_56, C_57)=k1_xboole_0 | k1_xboole_0!=B_56)), inference(superposition, [status(thm), theory('equality')], [c_211, c_56])).
% 2.66/1.42  tff(c_298, plain, (![B_58, C_59]: (k4_xboole_0(B_58, C_59)=k1_xboole_0 | k1_xboole_0!=B_58)), inference(superposition, [status(thm), theory('equality')], [c_250, c_104])).
% 2.66/1.42  tff(c_353, plain, (![C_59]: (k4_xboole_0(k1_xboole_0, C_59)=k3_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_298, c_104])).
% 2.66/1.42  tff(c_441, plain, (![C_68]: (k3_xboole_0(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_68), k1_xboole_0)=k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_68))), inference(resolution, [status(thm)], [c_332, c_10])).
% 2.66/1.42  tff(c_12, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k3_xboole_0(A_9, B_10), C_11)=k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.42  tff(c_453, plain, (![C_68, C_11]: (k3_xboole_0(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_68), k4_xboole_0(k1_xboole_0, C_11))=k4_xboole_0(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_68), C_11))), inference(superposition, [status(thm), theory('equality')], [c_441, c_12])).
% 2.66/1.42  tff(c_911, plain, (![C_91, C_92]: (k4_xboole_0(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_91), C_92)=k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_91))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_6, c_353, c_453])).
% 2.66/1.42  tff(c_982, plain, (![C_91, C_92]: (k3_xboole_0(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_91), C_92)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_911, c_56])).
% 2.66/1.42  tff(c_988, plain, (![C_60]: (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_982, c_336])).
% 2.66/1.42  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.42  tff(c_1113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_988, c_22])).
% 2.66/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  Inference rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Ref     : 0
% 2.66/1.42  #Sup     : 278
% 2.66/1.42  #Fact    : 0
% 2.66/1.42  #Define  : 0
% 2.66/1.42  #Split   : 0
% 2.66/1.42  #Chain   : 0
% 2.66/1.42  #Close   : 0
% 2.66/1.42  
% 2.66/1.42  Ordering : KBO
% 2.66/1.42  
% 2.66/1.42  Simplification rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Subsume      : 81
% 2.66/1.42  #Demod        : 57
% 2.66/1.42  #Tautology    : 100
% 2.66/1.42  #SimpNegUnit  : 0
% 2.66/1.42  #BackRed      : 5
% 2.66/1.42  
% 2.66/1.42  #Partial instantiations: 0
% 2.66/1.42  #Strategies tried      : 1
% 2.66/1.42  
% 2.66/1.42  Timing (in seconds)
% 2.66/1.42  ----------------------
% 2.66/1.42  Preprocessing        : 0.28
% 2.66/1.42  Parsing              : 0.15
% 2.66/1.42  CNF conversion       : 0.02
% 2.66/1.42  Main loop            : 0.36
% 2.66/1.42  Inferencing          : 0.14
% 2.66/1.42  Reduction            : 0.11
% 2.66/1.42  Demodulation         : 0.09
% 2.66/1.42  BG Simplification    : 0.02
% 2.66/1.42  Subsumption          : 0.06
% 2.66/1.42  Abstraction          : 0.02
% 2.66/1.42  MUC search           : 0.00
% 2.66/1.42  Cooper               : 0.00
% 2.66/1.42  Total                : 0.67
% 2.66/1.42  Index Insertion      : 0.00
% 2.66/1.42  Index Deletion       : 0.00
% 2.66/1.42  Index Matching       : 0.00
% 2.66/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
