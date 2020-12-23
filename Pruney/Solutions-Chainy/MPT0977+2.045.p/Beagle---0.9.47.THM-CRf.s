%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:51 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 136 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 215 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_90,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_647,plain,(
    ! [B_134,A_135] :
      ( v1_relat_1(B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_135))
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_656,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_647])).

tff(c_663,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_656])).

tff(c_927,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( r2_relset_1(A_174,B_175,C_176,C_176)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_951,plain,(
    ! [C_182] :
      ( r2_relset_1('#skF_1','#skF_2',C_182,C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_927])).

tff(c_966,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_951])).

tff(c_797,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_810,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_797])).

tff(c_824,plain,(
    ! [A_168,B_169,C_170] :
      ( m1_subset_1(k2_relset_1(A_168,B_169,C_170),k1_zfmisc_1(B_169))
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_848,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_824])).

tff(c_857,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_848])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_865,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_857,c_2])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k8_relat_1(A_10,B_11) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_868,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_865,c_12])).

tff(c_874,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_868])).

tff(c_34,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_partfun1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_32,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_994,plain,(
    ! [F_190,B_191,D_187,A_188,C_189,E_192] :
      ( k4_relset_1(A_188,B_191,C_189,D_187,E_192,F_190) = k5_relat_1(E_192,F_190)
      | ~ m1_subset_1(F_190,k1_zfmisc_1(k2_zfmisc_1(C_189,D_187)))
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_188,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1546,plain,(
    ! [A_270,B_271,A_272,E_273] :
      ( k4_relset_1(A_270,B_271,A_272,A_272,E_273,k6_partfun1(A_272)) = k5_relat_1(E_273,k6_partfun1(A_272))
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(resolution,[status(thm)],[c_32,c_994])).

tff(c_1568,plain,(
    ! [A_272] : k4_relset_1('#skF_1','#skF_2',A_272,A_272,'#skF_3',k6_partfun1(A_272)) = k5_relat_1('#skF_3',k6_partfun1(A_272)) ),
    inference(resolution,[status(thm)],[c_38,c_1546])).

tff(c_69,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_365,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( r2_relset_1(A_90,B_91,C_92,C_92)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_389,plain,(
    ! [C_98] :
      ( r2_relset_1('#skF_1','#skF_2',C_98,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_365])).

tff(c_404,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_389])).

tff(c_135,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_135])).

tff(c_161,plain,(
    ! [B_68,A_69] :
      ( k7_relat_1(B_68,A_69) = B_68
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_167,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_161])).

tff(c_173,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_167])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_partfun1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_432,plain,(
    ! [C_104,F_105,A_103,E_107,D_102,B_106] :
      ( k4_relset_1(A_103,B_106,C_104,D_102,E_107,F_105) = k5_relat_1(E_107,F_105)
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_104,D_102)))
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_103,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_482,plain,(
    ! [A_114,B_115,E_116] :
      ( k4_relset_1(A_114,B_115,'#skF_1','#skF_2',E_116,'#skF_3') = k5_relat_1(E_116,'#skF_3')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(resolution,[status(thm)],[c_38,c_432])).

tff(c_504,plain,(
    ! [A_35] : k4_relset_1(A_35,A_35,'#skF_1','#skF_2',k6_partfun1(A_35),'#skF_3') = k5_relat_1(k6_partfun1(A_35),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_482])).

tff(c_36,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_629,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_68])).

tff(c_641,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_629])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_404,c_173,c_641])).

tff(c_645,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1569,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_645])).

tff(c_1581,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1569])).

tff(c_1584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_966,c_874,c_1581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:20:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.53  
% 3.09/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.53  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.09/1.53  
% 3.09/1.53  %Foreground sorts:
% 3.09/1.53  
% 3.09/1.53  
% 3.09/1.53  %Background operators:
% 3.09/1.53  
% 3.09/1.53  
% 3.09/1.53  %Foreground operators:
% 3.09/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.09/1.53  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.09/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.09/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.09/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.09/1.53  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.09/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.09/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.09/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.09/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.09/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.53  
% 3.09/1.55  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.09/1.55  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 3.09/1.55  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.09/1.55  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.09/1.55  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.09/1.55  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.09/1.55  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.09/1.55  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 3.09/1.55  tff(f_90, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.09/1.55  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 3.09/1.55  tff(f_88, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.09/1.55  tff(f_78, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.09/1.55  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.55  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.09/1.55  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.09/1.55  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.55  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.09/1.55  tff(c_647, plain, (![B_134, A_135]: (v1_relat_1(B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(A_135)) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.09/1.55  tff(c_656, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_647])).
% 3.09/1.55  tff(c_663, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_656])).
% 3.09/1.55  tff(c_927, plain, (![A_174, B_175, C_176, D_177]: (r2_relset_1(A_174, B_175, C_176, C_176) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.55  tff(c_951, plain, (![C_182]: (r2_relset_1('#skF_1', '#skF_2', C_182, C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_927])).
% 3.09/1.55  tff(c_966, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_951])).
% 3.09/1.55  tff(c_797, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.09/1.55  tff(c_810, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_797])).
% 3.09/1.55  tff(c_824, plain, (![A_168, B_169, C_170]: (m1_subset_1(k2_relset_1(A_168, B_169, C_170), k1_zfmisc_1(B_169)) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.55  tff(c_848, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_810, c_824])).
% 3.09/1.55  tff(c_857, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_848])).
% 3.09/1.55  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.55  tff(c_865, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_857, c_2])).
% 3.09/1.55  tff(c_12, plain, (![A_10, B_11]: (k8_relat_1(A_10, B_11)=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.55  tff(c_868, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_865, c_12])).
% 3.09/1.55  tff(c_874, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_663, c_868])).
% 3.09/1.55  tff(c_34, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.09/1.55  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.09/1.55  tff(c_40, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_partfun1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 3.09/1.55  tff(c_32, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.09/1.55  tff(c_994, plain, (![F_190, B_191, D_187, A_188, C_189, E_192]: (k4_relset_1(A_188, B_191, C_189, D_187, E_192, F_190)=k5_relat_1(E_192, F_190) | ~m1_subset_1(F_190, k1_zfmisc_1(k2_zfmisc_1(C_189, D_187))) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_188, B_191))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.55  tff(c_1546, plain, (![A_270, B_271, A_272, E_273]: (k4_relset_1(A_270, B_271, A_272, A_272, E_273, k6_partfun1(A_272))=k5_relat_1(E_273, k6_partfun1(A_272)) | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(resolution, [status(thm)], [c_32, c_994])).
% 3.09/1.55  tff(c_1568, plain, (![A_272]: (k4_relset_1('#skF_1', '#skF_2', A_272, A_272, '#skF_3', k6_partfun1(A_272))=k5_relat_1('#skF_3', k6_partfun1(A_272)))), inference(resolution, [status(thm)], [c_38, c_1546])).
% 3.09/1.55  tff(c_69, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.09/1.55  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_69])).
% 3.09/1.55  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 3.09/1.55  tff(c_365, plain, (![A_90, B_91, C_92, D_93]: (r2_relset_1(A_90, B_91, C_92, C_92) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.55  tff(c_389, plain, (![C_98]: (r2_relset_1('#skF_1', '#skF_2', C_98, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_365])).
% 3.09/1.55  tff(c_404, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_389])).
% 3.09/1.55  tff(c_135, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.55  tff(c_148, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_135])).
% 3.09/1.55  tff(c_161, plain, (![B_68, A_69]: (k7_relat_1(B_68, A_69)=B_68 | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.55  tff(c_167, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_161])).
% 3.09/1.55  tff(c_173, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_167])).
% 3.09/1.55  tff(c_16, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.55  tff(c_39, plain, (![A_14, B_15]: (k5_relat_1(k6_partfun1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 3.09/1.55  tff(c_432, plain, (![C_104, F_105, A_103, E_107, D_102, B_106]: (k4_relset_1(A_103, B_106, C_104, D_102, E_107, F_105)=k5_relat_1(E_107, F_105) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_104, D_102))) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_103, B_106))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.55  tff(c_482, plain, (![A_114, B_115, E_116]: (k4_relset_1(A_114, B_115, '#skF_1', '#skF_2', E_116, '#skF_3')=k5_relat_1(E_116, '#skF_3') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(resolution, [status(thm)], [c_38, c_432])).
% 3.09/1.55  tff(c_504, plain, (![A_35]: (k4_relset_1(A_35, A_35, '#skF_1', '#skF_2', k6_partfun1(A_35), '#skF_3')=k5_relat_1(k6_partfun1(A_35), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_482])).
% 3.09/1.55  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.09/1.55  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 3.09/1.55  tff(c_629, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_68])).
% 3.09/1.55  tff(c_641, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39, c_629])).
% 3.09/1.55  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_404, c_173, c_641])).
% 3.09/1.55  tff(c_645, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.09/1.55  tff(c_1569, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_645])).
% 3.09/1.55  tff(c_1581, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1569])).
% 3.09/1.55  tff(c_1584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_663, c_966, c_874, c_1581])).
% 3.09/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.55  
% 3.09/1.55  Inference rules
% 3.09/1.55  ----------------------
% 3.09/1.55  #Ref     : 0
% 3.09/1.55  #Sup     : 323
% 3.09/1.55  #Fact    : 0
% 3.09/1.55  #Define  : 0
% 3.09/1.55  #Split   : 3
% 3.09/1.55  #Chain   : 0
% 3.09/1.55  #Close   : 0
% 3.09/1.55  
% 3.09/1.55  Ordering : KBO
% 3.09/1.55  
% 3.09/1.55  Simplification rules
% 3.09/1.55  ----------------------
% 3.09/1.55  #Subsume      : 29
% 3.09/1.55  #Demod        : 148
% 3.09/1.55  #Tautology    : 118
% 3.09/1.55  #SimpNegUnit  : 0
% 3.09/1.55  #BackRed      : 5
% 3.09/1.55  
% 3.09/1.55  #Partial instantiations: 0
% 3.09/1.55  #Strategies tried      : 1
% 3.09/1.55  
% 3.09/1.55  Timing (in seconds)
% 3.09/1.55  ----------------------
% 3.09/1.55  Preprocessing        : 0.31
% 3.09/1.55  Parsing              : 0.17
% 3.09/1.55  CNF conversion       : 0.02
% 3.09/1.55  Main loop            : 0.48
% 3.09/1.55  Inferencing          : 0.19
% 3.09/1.55  Reduction            : 0.15
% 3.09/1.55  Demodulation         : 0.11
% 3.09/1.55  BG Simplification    : 0.02
% 3.09/1.55  Subsumption          : 0.07
% 3.09/1.55  Abstraction          : 0.03
% 3.09/1.55  MUC search           : 0.00
% 3.09/1.55  Cooper               : 0.00
% 3.09/1.55  Total                : 0.82
% 3.09/1.55  Index Insertion      : 0.00
% 3.09/1.55  Index Deletion       : 0.00
% 3.09/1.55  Index Matching       : 0.00
% 3.09/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
