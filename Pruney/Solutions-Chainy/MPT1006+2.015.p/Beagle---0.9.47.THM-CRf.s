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
% DateTime   : Thu Dec  3 10:14:04 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 456 expanded)
%              Number of leaves         :   33 ( 170 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 697 expanded)
%              Number of equality atoms :   39 ( 267 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_39,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_39])).

tff(c_148,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_151,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_148])).

tff(c_157,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_151])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2])).

tff(c_162,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_76])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_2] : r1_tarski('#skF_1',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_6])).

tff(c_172,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_83])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_285,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k8_relset_1(A_52,B_53,C_54,D_55) = k10_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_421,plain,(
    ! [A_88,B_89,A_90,D_91] :
      ( k8_relset_1(A_88,B_89,A_90,D_91) = k10_relat_1(A_90,D_91)
      | ~ r1_tarski(A_90,k2_zfmisc_1(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_18,c_285])).

tff(c_429,plain,(
    ! [A_88,B_89,D_91] : k8_relset_1(A_88,B_89,'#skF_4',D_91) = k10_relat_1('#skF_4',D_91) ),
    inference(resolution,[status(thm)],[c_172,c_421])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_22])).

tff(c_171,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_162,c_84])).

tff(c_202,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_333,plain,(
    ! [A_64,B_65,A_66] :
      ( k1_relset_1(A_64,B_65,A_66) = k1_relat_1(A_66)
      | ~ r1_tarski(A_66,k2_zfmisc_1(A_64,B_65)) ) ),
    inference(resolution,[status(thm)],[c_18,c_202])).

tff(c_343,plain,(
    ! [A_64,B_65] : k1_relset_1(A_64,B_65,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_172,c_333])).

tff(c_345,plain,(
    ! [A_64,B_65] : k1_relset_1(A_64,B_65,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_343])).

tff(c_168,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_80])).

tff(c_79,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_12])).

tff(c_169,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_162,c_79])).

tff(c_373,plain,(
    ! [A_74,B_75,C_76] :
      ( k8_relset_1(A_74,B_75,C_76,B_75) = k1_relset_1(A_74,B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_489,plain,(
    ! [B_107,C_108] :
      ( k8_relset_1('#skF_4',B_107,C_108,B_107) = k1_relset_1('#skF_4',B_107,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_373])).

tff(c_491,plain,(
    ! [B_107] : k8_relset_1('#skF_4',B_107,'#skF_4',B_107) = k1_relset_1('#skF_4',B_107,'#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_489])).

tff(c_496,plain,(
    ! [B_107] : k10_relat_1('#skF_4',B_107) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_345,c_491])).

tff(c_355,plain,(
    ! [B_69,C_70,D_71] :
      ( k8_relset_1('#skF_4',B_69,C_70,D_71) = k10_relat_1(C_70,D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_285])).

tff(c_361,plain,(
    ! [B_69,D_71] : k8_relset_1('#skF_4',B_69,'#skF_4',D_71) = k10_relat_1('#skF_4',D_71) ),
    inference(resolution,[status(thm)],[c_168,c_355])).

tff(c_32,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_77,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_32])).

tff(c_165,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_162,c_77])).

tff(c_363,plain,(
    k10_relat_1('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_165])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.29  
% 2.35/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.29  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.29  
% 2.35/1.29  %Foreground sorts:
% 2.35/1.29  
% 2.35/1.29  
% 2.35/1.29  %Background operators:
% 2.35/1.29  
% 2.35/1.29  
% 2.35/1.29  %Foreground operators:
% 2.35/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.35/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.35/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.29  
% 2.35/1.30  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.35/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.35/1.30  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.35/1.30  tff(f_76, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.35/1.30  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.35/1.30  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.35/1.30  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.35/1.30  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.35/1.30  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.35/1.30  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.30  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.35/1.30  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.30  tff(c_71, plain, (![A_23]: (k1_xboole_0=A_23 | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.30  tff(c_75, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_71])).
% 2.35/1.30  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.30  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.35/1.30  tff(c_39, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 2.35/1.30  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_39])).
% 2.35/1.30  tff(c_148, plain, (![B_34, A_35]: (v1_xboole_0(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.35/1.30  tff(c_151, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_148])).
% 2.35/1.30  tff(c_157, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_151])).
% 2.35/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.30  tff(c_76, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2])).
% 2.35/1.30  tff(c_162, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_157, c_76])).
% 2.35/1.30  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.30  tff(c_83, plain, (![A_2]: (r1_tarski('#skF_1', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_6])).
% 2.35/1.30  tff(c_172, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_83])).
% 2.35/1.30  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.35/1.30  tff(c_285, plain, (![A_52, B_53, C_54, D_55]: (k8_relset_1(A_52, B_53, C_54, D_55)=k10_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.35/1.30  tff(c_421, plain, (![A_88, B_89, A_90, D_91]: (k8_relset_1(A_88, B_89, A_90, D_91)=k10_relat_1(A_90, D_91) | ~r1_tarski(A_90, k2_zfmisc_1(A_88, B_89)))), inference(resolution, [status(thm)], [c_18, c_285])).
% 2.35/1.30  tff(c_429, plain, (![A_88, B_89, D_91]: (k8_relset_1(A_88, B_89, '#skF_4', D_91)=k10_relat_1('#skF_4', D_91))), inference(resolution, [status(thm)], [c_172, c_421])).
% 2.35/1.30  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.30  tff(c_84, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_22])).
% 2.35/1.30  tff(c_171, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_162, c_84])).
% 2.35/1.30  tff(c_202, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.30  tff(c_333, plain, (![A_64, B_65, A_66]: (k1_relset_1(A_64, B_65, A_66)=k1_relat_1(A_66) | ~r1_tarski(A_66, k2_zfmisc_1(A_64, B_65)))), inference(resolution, [status(thm)], [c_18, c_202])).
% 2.35/1.30  tff(c_343, plain, (![A_64, B_65]: (k1_relset_1(A_64, B_65, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_172, c_333])).
% 2.35/1.30  tff(c_345, plain, (![A_64, B_65]: (k1_relset_1(A_64, B_65, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_343])).
% 2.35/1.30  tff(c_168, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_80])).
% 2.35/1.30  tff(c_79, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_12])).
% 2.35/1.30  tff(c_169, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_162, c_79])).
% 2.35/1.30  tff(c_373, plain, (![A_74, B_75, C_76]: (k8_relset_1(A_74, B_75, C_76, B_75)=k1_relset_1(A_74, B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.35/1.30  tff(c_489, plain, (![B_107, C_108]: (k8_relset_1('#skF_4', B_107, C_108, B_107)=k1_relset_1('#skF_4', B_107, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_169, c_373])).
% 2.35/1.30  tff(c_491, plain, (![B_107]: (k8_relset_1('#skF_4', B_107, '#skF_4', B_107)=k1_relset_1('#skF_4', B_107, '#skF_4'))), inference(resolution, [status(thm)], [c_168, c_489])).
% 2.35/1.30  tff(c_496, plain, (![B_107]: (k10_relat_1('#skF_4', B_107)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_345, c_491])).
% 2.35/1.30  tff(c_355, plain, (![B_69, C_70, D_71]: (k8_relset_1('#skF_4', B_69, C_70, D_71)=k10_relat_1(C_70, D_71) | ~m1_subset_1(C_70, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_169, c_285])).
% 2.35/1.30  tff(c_361, plain, (![B_69, D_71]: (k8_relset_1('#skF_4', B_69, '#skF_4', D_71)=k10_relat_1('#skF_4', D_71))), inference(resolution, [status(thm)], [c_168, c_355])).
% 2.35/1.30  tff(c_32, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.35/1.30  tff(c_77, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_32])).
% 2.35/1.30  tff(c_165, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_162, c_77])).
% 2.35/1.30  tff(c_363, plain, (k10_relat_1('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_165])).
% 2.35/1.30  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_496, c_363])).
% 2.35/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.30  
% 2.35/1.30  Inference rules
% 2.35/1.30  ----------------------
% 2.35/1.30  #Ref     : 0
% 2.35/1.30  #Sup     : 110
% 2.35/1.30  #Fact    : 0
% 2.35/1.30  #Define  : 0
% 2.35/1.30  #Split   : 0
% 2.35/1.30  #Chain   : 0
% 2.35/1.30  #Close   : 0
% 2.35/1.30  
% 2.35/1.30  Ordering : KBO
% 2.35/1.30  
% 2.35/1.30  Simplification rules
% 2.35/1.30  ----------------------
% 2.35/1.30  #Subsume      : 5
% 2.35/1.30  #Demod        : 66
% 2.35/1.30  #Tautology    : 79
% 2.35/1.30  #SimpNegUnit  : 0
% 2.35/1.30  #BackRed      : 25
% 2.35/1.30  
% 2.35/1.30  #Partial instantiations: 0
% 2.35/1.30  #Strategies tried      : 1
% 2.35/1.30  
% 2.35/1.30  Timing (in seconds)
% 2.35/1.30  ----------------------
% 2.35/1.31  Preprocessing        : 0.30
% 2.35/1.31  Parsing              : 0.16
% 2.35/1.31  CNF conversion       : 0.02
% 2.35/1.31  Main loop            : 0.24
% 2.35/1.31  Inferencing          : 0.09
% 2.35/1.31  Reduction            : 0.08
% 2.35/1.31  Demodulation         : 0.05
% 2.35/1.31  BG Simplification    : 0.02
% 2.35/1.31  Subsumption          : 0.04
% 2.35/1.31  Abstraction          : 0.02
% 2.35/1.31  MUC search           : 0.00
% 2.35/1.31  Cooper               : 0.00
% 2.35/1.31  Total                : 0.57
% 2.35/1.31  Index Insertion      : 0.00
% 2.35/1.31  Index Deletion       : 0.00
% 2.35/1.31  Index Matching       : 0.00
% 2.35/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
