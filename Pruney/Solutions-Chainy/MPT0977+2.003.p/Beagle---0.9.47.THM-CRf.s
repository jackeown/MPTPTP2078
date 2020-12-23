%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:45 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 100 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 158 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_58,plain,(
    ! [C_37,B_38,A_39] :
      ( v5_relat_1(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_257,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_relset_1(A_94,B_95,D_96,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_263,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_257])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_231,plain,(
    ! [B_90,A_91] :
      ( k5_relat_1(B_90,k6_partfun1(A_91)) = B_90
      | ~ r1_tarski(k2_relat_1(B_90),A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_235,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_26,plain,(
    ! [A_25] : m1_subset_1(k6_relat_1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_33,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_291,plain,(
    ! [E_108,C_104,A_109,F_107,D_105,B_106] :
      ( k4_relset_1(A_109,B_106,C_104,D_105,E_108,F_107) = k5_relat_1(E_108,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_104,D_105)))
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_311,plain,(
    ! [A_113,B_114,A_115,E_116] :
      ( k4_relset_1(A_113,B_114,A_115,A_115,E_116,k6_partfun1(A_115)) = k5_relat_1(E_116,k6_partfun1(A_115))
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(resolution,[status(thm)],[c_33,c_291])).

tff(c_317,plain,(
    ! [A_115] : k4_relset_1('#skF_1','#skF_2',A_115,A_115,'#skF_3',k6_partfun1(A_115)) = k5_relat_1('#skF_3',k6_partfun1(A_115)) ),
    inference(resolution,[status(thm)],[c_32,c_311])).

tff(c_79,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_103,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_relset_1(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_109,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(k6_partfun1(A_48),B_49) = B_49
      | ~ r1_tarski(k1_relat_1(B_49),A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_92,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_partfun1(A_1),B_2) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_158,plain,(
    ! [F_70,C_67,A_72,D_68,B_69,E_71] :
      ( k4_relset_1(A_72,B_69,C_67,D_68,E_71,F_70) = k5_relat_1(E_71,F_70)
      | ~ m1_subset_1(F_70,k1_zfmisc_1(k2_zfmisc_1(C_67,D_68)))
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_165,plain,(
    ! [A_73,B_74,E_75] :
      ( k4_relset_1(A_73,B_74,'#skF_1','#skF_2',E_75,'#skF_3') = k5_relat_1(E_75,'#skF_3')
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_32,c_158])).

tff(c_172,plain,(
    ! [A_25] : k4_relset_1(A_25,A_25,'#skF_1','#skF_2',k6_partfun1(A_25),'#skF_3') = k5_relat_1(k6_partfun1(A_25),'#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_165])).

tff(c_30,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_67,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_178,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_67])).

tff(c_190,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_178])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_87,c_109,c_190])).

tff(c_194,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_338,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_194])).

tff(c_350,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_338])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66,c_263,c_350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.67  
% 2.83/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.67  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.83/1.67  
% 2.83/1.67  %Foreground sorts:
% 2.83/1.67  
% 2.83/1.67  
% 2.83/1.67  %Background operators:
% 2.83/1.67  
% 2.83/1.67  
% 2.83/1.67  %Foreground operators:
% 2.83/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.83/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.83/1.67  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.67  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.67  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.67  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.83/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.83/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.83/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.83/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.67  
% 2.83/1.68  tff(f_84, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.83/1.68  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.68  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.83/1.68  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.83/1.68  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.83/1.68  tff(f_77, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.83/1.68  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.83/1.68  tff(f_75, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.83/1.68  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.83/1.68  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.83/1.68  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.83/1.68  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.68  tff(c_46, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.68  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_46])).
% 2.83/1.68  tff(c_58, plain, (![C_37, B_38, A_39]: (v5_relat_1(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_38))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.68  tff(c_66, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_58])).
% 2.83/1.68  tff(c_257, plain, (![A_94, B_95, D_96]: (r2_relset_1(A_94, B_95, D_96, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.68  tff(c_263, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_257])).
% 2.83/1.68  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.68  tff(c_28, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.83/1.68  tff(c_12, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.68  tff(c_231, plain, (![B_90, A_91]: (k5_relat_1(B_90, k6_partfun1(A_91))=B_90 | ~r1_tarski(k2_relat_1(B_90), A_91) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 2.83/1.68  tff(c_235, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_8, c_231])).
% 2.83/1.68  tff(c_26, plain, (![A_25]: (m1_subset_1(k6_relat_1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.83/1.68  tff(c_33, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.83/1.68  tff(c_291, plain, (![E_108, C_104, A_109, F_107, D_105, B_106]: (k4_relset_1(A_109, B_106, C_104, D_105, E_108, F_107)=k5_relat_1(E_108, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_104, D_105))) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_106))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.68  tff(c_311, plain, (![A_113, B_114, A_115, E_116]: (k4_relset_1(A_113, B_114, A_115, A_115, E_116, k6_partfun1(A_115))=k5_relat_1(E_116, k6_partfun1(A_115)) | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(resolution, [status(thm)], [c_33, c_291])).
% 2.83/1.68  tff(c_317, plain, (![A_115]: (k4_relset_1('#skF_1', '#skF_2', A_115, A_115, '#skF_3', k6_partfun1(A_115))=k5_relat_1('#skF_3', k6_partfun1(A_115)))), inference(resolution, [status(thm)], [c_32, c_311])).
% 2.83/1.68  tff(c_79, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.68  tff(c_87, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_79])).
% 2.83/1.68  tff(c_103, plain, (![A_53, B_54, D_55]: (r2_relset_1(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.68  tff(c_109, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_103])).
% 2.83/1.68  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.68  tff(c_10, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.68  tff(c_88, plain, (![A_48, B_49]: (k5_relat_1(k6_partfun1(A_48), B_49)=B_49 | ~r1_tarski(k1_relat_1(B_49), A_48) | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10])).
% 2.83/1.68  tff(c_92, plain, (![A_1, B_2]: (k5_relat_1(k6_partfun1(A_1), B_2)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_88])).
% 2.83/1.68  tff(c_158, plain, (![F_70, C_67, A_72, D_68, B_69, E_71]: (k4_relset_1(A_72, B_69, C_67, D_68, E_71, F_70)=k5_relat_1(E_71, F_70) | ~m1_subset_1(F_70, k1_zfmisc_1(k2_zfmisc_1(C_67, D_68))) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_69))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.68  tff(c_165, plain, (![A_73, B_74, E_75]: (k4_relset_1(A_73, B_74, '#skF_1', '#skF_2', E_75, '#skF_3')=k5_relat_1(E_75, '#skF_3') | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_32, c_158])).
% 2.83/1.68  tff(c_172, plain, (![A_25]: (k4_relset_1(A_25, A_25, '#skF_1', '#skF_2', k6_partfun1(A_25), '#skF_3')=k5_relat_1(k6_partfun1(A_25), '#skF_3'))), inference(resolution, [status(thm)], [c_33, c_165])).
% 2.83/1.68  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.68  tff(c_67, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.83/1.68  tff(c_178, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_67])).
% 2.83/1.68  tff(c_190, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_178])).
% 2.83/1.68  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_87, c_109, c_190])).
% 2.83/1.68  tff(c_194, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.83/1.68  tff(c_338, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_194])).
% 2.83/1.68  tff(c_350, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_235, c_338])).
% 2.83/1.68  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_66, c_263, c_350])).
% 2.83/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.68  
% 2.83/1.68  Inference rules
% 2.83/1.68  ----------------------
% 2.83/1.68  #Ref     : 0
% 2.83/1.68  #Sup     : 65
% 2.83/1.68  #Fact    : 0
% 2.83/1.68  #Define  : 0
% 2.83/1.68  #Split   : 1
% 2.83/1.68  #Chain   : 0
% 2.83/1.68  #Close   : 0
% 2.83/1.68  
% 2.83/1.68  Ordering : KBO
% 2.83/1.68  
% 2.83/1.68  Simplification rules
% 2.83/1.68  ----------------------
% 2.83/1.68  #Subsume      : 2
% 2.83/1.68  #Demod        : 31
% 2.83/1.68  #Tautology    : 31
% 2.83/1.68  #SimpNegUnit  : 0
% 2.83/1.68  #BackRed      : 3
% 2.83/1.68  
% 2.83/1.68  #Partial instantiations: 0
% 2.83/1.68  #Strategies tried      : 1
% 2.83/1.69  
% 2.83/1.69  Timing (in seconds)
% 2.83/1.69  ----------------------
% 2.83/1.69  Preprocessing        : 0.51
% 2.83/1.69  Parsing              : 0.27
% 2.83/1.69  CNF conversion       : 0.03
% 2.83/1.69  Main loop            : 0.34
% 2.83/1.69  Inferencing          : 0.13
% 2.83/1.69  Reduction            : 0.10
% 2.83/1.69  Demodulation         : 0.08
% 2.83/1.69  BG Simplification    : 0.02
% 2.83/1.69  Subsumption          : 0.05
% 2.83/1.69  Abstraction          : 0.02
% 2.83/1.69  MUC search           : 0.00
% 2.83/1.69  Cooper               : 0.00
% 2.83/1.69  Total                : 0.89
% 2.83/1.69  Index Insertion      : 0.00
% 2.83/1.69  Index Deletion       : 0.00
% 2.83/1.69  Index Matching       : 0.00
% 2.83/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
