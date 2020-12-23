%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:12 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 108 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 164 expanded)
%              Number of equality atoms :   28 (  82 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
          & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_37,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_37])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_22,B_23,C_24] :
      ( k3_relset_1(A_22,B_23,C_24) = k4_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_42])).

tff(c_167,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1(k3_relset_1(A_40,B_41,C_42),k1_zfmisc_1(k2_zfmisc_1(B_41,A_40)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,
    ( m1_subset_1(k4_relat_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_167])).

tff(c_188,plain,(
    m1_subset_1(k4_relat_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_182])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_201,plain,(
    k2_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_188,c_12])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_31,B_32,C_33] :
      ( m1_subset_1(k3_relset_1(A_31,B_32,C_33),k1_zfmisc_1(k2_zfmisc_1(B_32,A_31)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,
    ( m1_subset_1(k4_relat_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_72])).

tff(c_93,plain,(
    m1_subset_1(k4_relat_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_87])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) = k1_relat_1(k4_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_93,c_10])).

tff(c_62,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_51,plain,(
    ! [A_25,B_26,C_27] :
      ( k1_relset_1(A_25,B_26,C_27) = k1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_16,plain,
    ( k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,
    ( k2_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k1_relat_1('#skF_3')
    | k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_55,c_46,c_16])).

tff(c_61,plain,(
    k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_67,plain,(
    k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_61])).

tff(c_139,plain,(
    k1_relat_1(k4_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_67])).

tff(c_146,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_139])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_146])).

tff(c_151,plain,(
    k2_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_231,plain,(
    k2_relat_1(k4_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_151])).

tff(c_238,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_231])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  %$ m1_subset_1 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.21  
% 1.99/1.21  %Foreground sorts:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Background operators:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Foreground operators:
% 1.99/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.21  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 1.99/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.99/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.21  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.99/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.21  
% 1.99/1.22  tff(f_58, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 1.99/1.22  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.99/1.22  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.99/1.22  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 1.99/1.22  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 1.99/1.22  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.99/1.22  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.99/1.22  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.22  tff(c_37, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.22  tff(c_41, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_37])).
% 1.99/1.22  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.22  tff(c_42, plain, (![A_22, B_23, C_24]: (k3_relset_1(A_22, B_23, C_24)=k4_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.22  tff(c_46, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_42])).
% 1.99/1.22  tff(c_167, plain, (![A_40, B_41, C_42]: (m1_subset_1(k3_relset_1(A_40, B_41, C_42), k1_zfmisc_1(k2_zfmisc_1(B_41, A_40))) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.22  tff(c_182, plain, (m1_subset_1(k4_relat_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_167])).
% 1.99/1.22  tff(c_188, plain, (m1_subset_1(k4_relat_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_182])).
% 1.99/1.22  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.22  tff(c_201, plain, (k2_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_188, c_12])).
% 1.99/1.22  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.22  tff(c_72, plain, (![A_31, B_32, C_33]: (m1_subset_1(k3_relset_1(A_31, B_32, C_33), k1_zfmisc_1(k2_zfmisc_1(B_32, A_31))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.22  tff(c_87, plain, (m1_subset_1(k4_relat_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_72])).
% 1.99/1.22  tff(c_93, plain, (m1_subset_1(k4_relat_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_87])).
% 1.99/1.22  tff(c_10, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.22  tff(c_121, plain, (k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))=k1_relat_1(k4_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_93, c_10])).
% 1.99/1.22  tff(c_62, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.22  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_62])).
% 1.99/1.22  tff(c_51, plain, (![A_25, B_26, C_27]: (k1_relset_1(A_25, B_26, C_27)=k1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.22  tff(c_55, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_51])).
% 1.99/1.22  tff(c_16, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.22  tff(c_60, plain, (k2_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3') | k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_55, c_46, c_16])).
% 1.99/1.22  tff(c_61, plain, (k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 1.99/1.22  tff(c_67, plain, (k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_61])).
% 1.99/1.22  tff(c_139, plain, (k1_relat_1(k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_67])).
% 1.99/1.22  tff(c_146, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_139])).
% 1.99/1.22  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_146])).
% 1.99/1.22  tff(c_151, plain, (k2_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 1.99/1.22  tff(c_231, plain, (k2_relat_1(k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_151])).
% 1.99/1.22  tff(c_238, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_231])).
% 1.99/1.22  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_238])).
% 1.99/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  Inference rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Ref     : 0
% 1.99/1.22  #Sup     : 58
% 1.99/1.22  #Fact    : 0
% 1.99/1.22  #Define  : 0
% 1.99/1.22  #Split   : 1
% 1.99/1.22  #Chain   : 0
% 1.99/1.22  #Close   : 0
% 1.99/1.22  
% 1.99/1.22  Ordering : KBO
% 1.99/1.22  
% 1.99/1.22  Simplification rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Subsume      : 0
% 1.99/1.22  #Demod        : 19
% 1.99/1.22  #Tautology    : 29
% 1.99/1.22  #SimpNegUnit  : 0
% 1.99/1.22  #BackRed      : 4
% 1.99/1.22  
% 1.99/1.22  #Partial instantiations: 0
% 1.99/1.22  #Strategies tried      : 1
% 1.99/1.22  
% 1.99/1.22  Timing (in seconds)
% 1.99/1.22  ----------------------
% 1.99/1.22  Preprocessing        : 0.29
% 1.99/1.22  Parsing              : 0.16
% 1.99/1.22  CNF conversion       : 0.02
% 1.99/1.22  Main loop            : 0.18
% 1.99/1.22  Inferencing          : 0.07
% 1.99/1.22  Reduction            : 0.05
% 1.99/1.22  Demodulation         : 0.04
% 1.99/1.22  BG Simplification    : 0.01
% 1.99/1.22  Subsumption          : 0.02
% 1.99/1.22  Abstraction          : 0.01
% 1.99/1.22  MUC search           : 0.00
% 1.99/1.23  Cooper               : 0.00
% 1.99/1.23  Total                : 0.50
% 1.99/1.23  Index Insertion      : 0.00
% 1.99/1.23  Index Deletion       : 0.00
% 1.99/1.23  Index Matching       : 0.00
% 1.99/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
