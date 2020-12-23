%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:48 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 112 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 182 expanded)
%              Number of equality atoms :   17 (  24 expanded)
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_47,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_59,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_211,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_219,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_211])).

tff(c_266,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r2_relset_1(A_100,B_101,C_102,C_102)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_278,plain,(
    ! [C_107] :
      ( r2_relset_1('#skF_1','#skF_2',C_107,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_266])).

tff(c_281,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_278])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_226,plain,(
    ! [B_92,A_93] :
      ( k5_relat_1(B_92,k6_partfun1(A_93)) = B_92
      | ~ r1_tarski(k2_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_230,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_partfun1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_26,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_33,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_290,plain,(
    ! [C_110,E_115,F_113,A_111,D_114,B_112] :
      ( k4_relset_1(A_111,B_112,C_110,D_114,E_115,F_113) = k5_relat_1(E_115,F_113)
      | ~ m1_subset_1(F_113,k1_zfmisc_1(k2_zfmisc_1(C_110,D_114)))
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_325,plain,(
    ! [A_120,B_121,A_122,E_123] :
      ( k4_relset_1(A_120,B_121,A_122,A_122,E_123,k6_partfun1(A_122)) = k5_relat_1(E_123,k6_partfun1(A_122))
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(resolution,[status(thm)],[c_33,c_290])).

tff(c_331,plain,(
    ! [A_122] : k4_relset_1('#skF_1','#skF_2',A_122,A_122,'#skF_3',k6_partfun1(A_122)) = k5_relat_1('#skF_3',k6_partfun1(A_122)) ),
    inference(resolution,[status(thm)],[c_32,c_325])).

tff(c_64,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_142,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r2_relset_1(A_62,B_63,C_64,C_64)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154,plain,(
    ! [C_69] :
      ( r2_relset_1('#skF_1','#skF_2',C_69,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_142])).

tff(c_157,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_94,plain,(
    ! [A_52,B_53] :
      ( k5_relat_1(k6_partfun1(A_52),B_53) = B_53
      | ~ r1_tarski(k1_relat_1(B_53),A_52)
      | ~ v1_relat_1(B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_98,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_158,plain,(
    ! [D_74,C_70,B_72,E_75,A_71,F_73] :
      ( k4_relset_1(A_71,B_72,C_70,D_74,E_75,F_73) = k5_relat_1(E_75,F_73)
      | ~ m1_subset_1(F_73,k1_zfmisc_1(k2_zfmisc_1(C_70,D_74)))
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_165,plain,(
    ! [A_76,B_77,E_78] :
      ( k4_relset_1(A_76,B_77,'#skF_1','#skF_2',E_78,'#skF_3') = k5_relat_1(E_78,'#skF_3')
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(resolution,[status(thm)],[c_32,c_158])).

tff(c_172,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_165])).

tff(c_30,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_63,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_178,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_63])).

tff(c_190,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_178])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_72,c_157,c_190])).

tff(c_194,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_332,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_194])).

tff(c_344,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_332])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_219,c_281,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 10:09:34 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.20  
% 2.14/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.21  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.21  
% 2.14/1.21  %Foreground sorts:
% 2.14/1.21  
% 2.14/1.21  
% 2.14/1.21  %Background operators:
% 2.14/1.21  
% 2.14/1.21  
% 2.14/1.21  %Foreground operators:
% 2.14/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.14/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.14/1.21  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.14/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.14/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.21  
% 2.14/1.22  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.14/1.22  tff(f_87, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.14/1.22  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.14/1.22  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.22  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.14/1.22  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.14/1.22  tff(f_80, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.14/1.22  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.14/1.22  tff(f_78, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.14/1.22  tff(f_70, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.14/1.22  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.14/1.22  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.14/1.22  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.22  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.22  tff(c_47, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.22  tff(c_53, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.14/1.22  tff(c_59, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_53])).
% 2.14/1.22  tff(c_211, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.22  tff(c_219, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_211])).
% 2.14/1.22  tff(c_266, plain, (![A_100, B_101, C_102, D_103]: (r2_relset_1(A_100, B_101, C_102, C_102) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.22  tff(c_278, plain, (![C_107]: (r2_relset_1('#skF_1', '#skF_2', C_107, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_266])).
% 2.14/1.22  tff(c_281, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_278])).
% 2.14/1.22  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.22  tff(c_28, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.14/1.22  tff(c_16, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.22  tff(c_226, plain, (![B_92, A_93]: (k5_relat_1(B_92, k6_partfun1(A_93))=B_92 | ~r1_tarski(k2_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_16])).
% 2.14/1.22  tff(c_230, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_partfun1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_226])).
% 2.14/1.22  tff(c_26, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.22  tff(c_33, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.14/1.22  tff(c_290, plain, (![C_110, E_115, F_113, A_111, D_114, B_112]: (k4_relset_1(A_111, B_112, C_110, D_114, E_115, F_113)=k5_relat_1(E_115, F_113) | ~m1_subset_1(F_113, k1_zfmisc_1(k2_zfmisc_1(C_110, D_114))) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.22  tff(c_325, plain, (![A_120, B_121, A_122, E_123]: (k4_relset_1(A_120, B_121, A_122, A_122, E_123, k6_partfun1(A_122))=k5_relat_1(E_123, k6_partfun1(A_122)) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(resolution, [status(thm)], [c_33, c_290])).
% 2.14/1.22  tff(c_331, plain, (![A_122]: (k4_relset_1('#skF_1', '#skF_2', A_122, A_122, '#skF_3', k6_partfun1(A_122))=k5_relat_1('#skF_3', k6_partfun1(A_122)))), inference(resolution, [status(thm)], [c_32, c_325])).
% 2.14/1.22  tff(c_64, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.22  tff(c_72, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_64])).
% 2.14/1.22  tff(c_142, plain, (![A_62, B_63, C_64, D_65]: (r2_relset_1(A_62, B_63, C_64, C_64) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.22  tff(c_154, plain, (![C_69]: (r2_relset_1('#skF_1', '#skF_2', C_69, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_142])).
% 2.14/1.22  tff(c_157, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_154])).
% 2.14/1.22  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.22  tff(c_14, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.22  tff(c_94, plain, (![A_52, B_53]: (k5_relat_1(k6_partfun1(A_52), B_53)=B_53 | ~r1_tarski(k1_relat_1(B_53), A_52) | ~v1_relat_1(B_53))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14])).
% 2.14/1.22  tff(c_98, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_94])).
% 2.14/1.22  tff(c_158, plain, (![D_74, C_70, B_72, E_75, A_71, F_73]: (k4_relset_1(A_71, B_72, C_70, D_74, E_75, F_73)=k5_relat_1(E_75, F_73) | ~m1_subset_1(F_73, k1_zfmisc_1(k2_zfmisc_1(C_70, D_74))) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.22  tff(c_165, plain, (![A_76, B_77, E_78]: (k4_relset_1(A_76, B_77, '#skF_1', '#skF_2', E_78, '#skF_3')=k5_relat_1(E_78, '#skF_3') | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(resolution, [status(thm)], [c_32, c_158])).
% 2.14/1.22  tff(c_172, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_33, c_165])).
% 2.14/1.22  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.22  tff(c_63, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.14/1.22  tff(c_178, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_63])).
% 2.14/1.22  tff(c_190, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98, c_178])).
% 2.14/1.22  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_72, c_157, c_190])).
% 2.14/1.22  tff(c_194, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.14/1.22  tff(c_332, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_194])).
% 2.14/1.22  tff(c_344, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_230, c_332])).
% 2.14/1.22  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_219, c_281, c_344])).
% 2.14/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.22  
% 2.14/1.22  Inference rules
% 2.14/1.22  ----------------------
% 2.14/1.22  #Ref     : 0
% 2.14/1.22  #Sup     : 65
% 2.14/1.22  #Fact    : 0
% 2.14/1.22  #Define  : 0
% 2.14/1.22  #Split   : 1
% 2.14/1.22  #Chain   : 0
% 2.14/1.22  #Close   : 0
% 2.14/1.22  
% 2.14/1.22  Ordering : KBO
% 2.14/1.22  
% 2.14/1.22  Simplification rules
% 2.14/1.22  ----------------------
% 2.14/1.22  #Subsume      : 2
% 2.14/1.22  #Demod        : 27
% 2.14/1.22  #Tautology    : 27
% 2.14/1.22  #SimpNegUnit  : 0
% 2.14/1.22  #BackRed      : 3
% 2.14/1.22  
% 2.14/1.22  #Partial instantiations: 0
% 2.14/1.22  #Strategies tried      : 1
% 2.14/1.22  
% 2.14/1.22  Timing (in seconds)
% 2.14/1.22  ----------------------
% 2.14/1.23  Preprocessing        : 0.32
% 2.14/1.23  Parsing              : 0.18
% 2.14/1.23  CNF conversion       : 0.02
% 2.14/1.23  Main loop            : 0.25
% 2.14/1.23  Inferencing          : 0.10
% 2.14/1.23  Reduction            : 0.07
% 2.14/1.23  Demodulation         : 0.05
% 2.14/1.23  BG Simplification    : 0.01
% 2.14/1.23  Subsumption          : 0.03
% 2.14/1.23  Abstraction          : 0.02
% 2.14/1.23  MUC search           : 0.00
% 2.14/1.23  Cooper               : 0.00
% 2.14/1.23  Total                : 0.61
% 2.14/1.23  Index Insertion      : 0.00
% 2.14/1.23  Index Deletion       : 0.00
% 2.14/1.23  Index Matching       : 0.00
% 2.14/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
