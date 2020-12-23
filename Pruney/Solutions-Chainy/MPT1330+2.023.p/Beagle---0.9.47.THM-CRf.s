%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:12 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 548 expanded)
%              Number of leaves         :   47 ( 207 expanded)
%              Depth                    :   11
%              Number of atoms          :  173 (1241 expanded)
%              Number of equality atoms :   73 ( 538 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_79,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_120,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(c_22,plain,(
    ! [A_15] : k10_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1816,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k8_relset_1(A_229,B_230,C_231,D_232) = k10_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1823,plain,(
    ! [A_229,B_230,D_232] : k8_relset_1(A_229,B_230,k1_xboole_0,D_232) = k10_relat_1(k1_xboole_0,D_232) ),
    inference(resolution,[status(thm)],[c_8,c_1816])).

tff(c_1827,plain,(
    ! [A_233,B_234,D_235] : k8_relset_1(A_233,B_234,k1_xboole_0,D_235) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1823])).

tff(c_89,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_95,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_36])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_175,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_183,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_175])).

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_182,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_175])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_194,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_182,c_62])).

tff(c_206,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_209,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_194,c_206])).

tff(c_215,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_209])).

tff(c_278,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_292,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_194,c_278])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( k5_relat_1(B_21,k6_relat_1(A_20)) = B_21
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_363,plain,(
    ! [B_91,A_92] :
      ( k5_relat_1(B_91,k6_partfun1(A_92)) = B_91
      | ~ r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_34])).

tff(c_373,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_partfun1(A_10)) = B_11
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_363])).

tff(c_18,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    ! [A_12] : v1_relat_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_30,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_73,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_30])).

tff(c_836,plain,(
    ! [A_135,B_136] :
      ( k10_relat_1(A_135,k1_relat_1(B_136)) = k1_relat_1(k5_relat_1(A_135,B_136))
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_849,plain,(
    ! [A_135,A_19] :
      ( k1_relat_1(k5_relat_1(A_135,k6_partfun1(A_19))) = k10_relat_1(A_135,A_19)
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_836])).

tff(c_953,plain,(
    ! [A_140,A_141] :
      ( k1_relat_1(k5_relat_1(A_140,k6_partfun1(A_141))) = k10_relat_1(A_140,A_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_849])).

tff(c_1022,plain,(
    ! [B_144,A_145] :
      ( k10_relat_1(B_144,A_145) = k1_relat_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v5_relat_1(B_144,A_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_953])).

tff(c_1025,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_292,c_1022])).

tff(c_1034,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_1025])).

tff(c_255,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_269,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_194,c_255])).

tff(c_493,plain,(
    ! [B_101,A_102] :
      ( k1_relat_1(B_101) = A_102
      | ~ v1_partfun1(B_101,A_102)
      | ~ v4_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_496,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_269,c_493])).

tff(c_502,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_496])).

tff(c_512,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_60,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_110,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_184,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_64])).

tff(c_193,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_184])).

tff(c_763,plain,(
    ! [B_131,C_132,A_133] :
      ( k1_xboole_0 = B_131
      | v1_partfun1(C_132,A_133)
      | ~ v1_funct_2(C_132,A_133,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_131)))
      | ~ v1_funct_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_766,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_763])).

tff(c_779,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_193,c_766])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_110,c_779])).

tff(c_782,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_788,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_194])).

tff(c_1106,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k8_relset_1(A_150,B_151,C_152,D_153) = k10_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1116,plain,(
    ! [D_153] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_153) = k10_relat_1('#skF_3',D_153) ),
    inference(resolution,[status(thm)],[c_788,c_1106])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_218,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_182,c_58])).

tff(c_787,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_782,c_218])).

tff(c_1119,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_787])).

tff(c_1122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1119])).

tff(c_1124,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1197,plain,(
    ! [A_162] :
      ( u1_struct_0(A_162) = k2_struct_0(A_162)
      | ~ l1_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1200,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1197])).

tff(c_1205,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1200])).

tff(c_1217,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1205,c_62])).

tff(c_1490,plain,(
    ! [A_210,B_211] :
      ( k8_relset_1(A_210,A_210,k6_partfun1(A_210),B_211) = B_211
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_210)) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1492,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1217,c_1490])).

tff(c_1496,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1492])).

tff(c_1831,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1827,c_1496])).

tff(c_1825,plain,(
    ! [A_229,B_230,D_232] : k8_relset_1(A_229,B_230,k1_xboole_0,D_232) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1823])).

tff(c_1838,plain,(
    ! [A_229,B_230,D_232] : k8_relset_1(A_229,B_230,'#skF_3',D_232) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_1831,c_1825])).

tff(c_1123,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1203,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1197])).

tff(c_1207,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1203])).

tff(c_1242,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_1205,c_1124,c_1123,c_58])).

tff(c_1863,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_1831,c_1831,c_1831,c_1242])).

tff(c_2201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1838,c_1863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:07:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.64  
% 3.96/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.96/1.64  
% 3.96/1.64  %Foreground sorts:
% 3.96/1.64  
% 3.96/1.64  
% 3.96/1.64  %Background operators:
% 3.96/1.64  
% 3.96/1.64  
% 3.96/1.64  %Foreground operators:
% 3.96/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.96/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.64  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.96/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.96/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.96/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.96/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.96/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.96/1.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.96/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.96/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.96/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.96/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.96/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.96/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.64  
% 3.96/1.66  tff(f_58, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 3.96/1.66  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.96/1.66  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.96/1.66  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.96/1.66  tff(f_79, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.96/1.66  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.96/1.66  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.96/1.66  tff(f_143, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.96/1.66  tff(f_124, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.96/1.66  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.96/1.66  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.96/1.66  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.96/1.66  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.96/1.66  tff(f_54, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.96/1.66  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.96/1.66  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.96/1.66  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.96/1.66  tff(f_116, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 3.96/1.66  tff(f_120, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 3.96/1.66  tff(c_22, plain, (![A_15]: (k10_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.96/1.66  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.96/1.66  tff(c_1816, plain, (![A_229, B_230, C_231, D_232]: (k8_relset_1(A_229, B_230, C_231, D_232)=k10_relat_1(C_231, D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.96/1.66  tff(c_1823, plain, (![A_229, B_230, D_232]: (k8_relset_1(A_229, B_230, k1_xboole_0, D_232)=k10_relat_1(k1_xboole_0, D_232))), inference(resolution, [status(thm)], [c_8, c_1816])).
% 3.96/1.66  tff(c_1827, plain, (![A_233, B_234, D_235]: (k8_relset_1(A_233, B_234, k1_xboole_0, D_235)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1823])).
% 3.96/1.66  tff(c_89, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.96/1.66  tff(c_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.96/1.66  tff(c_95, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89, c_36])).
% 3.96/1.66  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.66  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.96/1.66  tff(c_70, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.66  tff(c_175, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.96/1.66  tff(c_183, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_175])).
% 3.96/1.66  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.66  tff(c_182, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_175])).
% 3.96/1.66  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.66  tff(c_194, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_182, c_62])).
% 3.96/1.66  tff(c_206, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.96/1.66  tff(c_209, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_194, c_206])).
% 3.96/1.66  tff(c_215, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_209])).
% 3.96/1.66  tff(c_278, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.96/1.66  tff(c_292, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_194, c_278])).
% 3.96/1.66  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.96/1.66  tff(c_48, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.96/1.66  tff(c_34, plain, (![B_21, A_20]: (k5_relat_1(B_21, k6_relat_1(A_20))=B_21 | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.96/1.66  tff(c_363, plain, (![B_91, A_92]: (k5_relat_1(B_91, k6_partfun1(A_92))=B_91 | ~r1_tarski(k2_relat_1(B_91), A_92) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_34])).
% 3.96/1.66  tff(c_373, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_partfun1(A_10))=B_11 | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_16, c_363])).
% 3.96/1.66  tff(c_18, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.96/1.66  tff(c_74, plain, (![A_12]: (v1_relat_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18])).
% 3.96/1.66  tff(c_30, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.66  tff(c_73, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_30])).
% 3.96/1.66  tff(c_836, plain, (![A_135, B_136]: (k10_relat_1(A_135, k1_relat_1(B_136))=k1_relat_1(k5_relat_1(A_135, B_136)) | ~v1_relat_1(B_136) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.96/1.66  tff(c_849, plain, (![A_135, A_19]: (k1_relat_1(k5_relat_1(A_135, k6_partfun1(A_19)))=k10_relat_1(A_135, A_19) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_73, c_836])).
% 3.96/1.66  tff(c_953, plain, (![A_140, A_141]: (k1_relat_1(k5_relat_1(A_140, k6_partfun1(A_141)))=k10_relat_1(A_140, A_141) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_849])).
% 3.96/1.66  tff(c_1022, plain, (![B_144, A_145]: (k10_relat_1(B_144, A_145)=k1_relat_1(B_144) | ~v1_relat_1(B_144) | ~v5_relat_1(B_144, A_145) | ~v1_relat_1(B_144))), inference(superposition, [status(thm), theory('equality')], [c_373, c_953])).
% 3.96/1.66  tff(c_1025, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_292, c_1022])).
% 3.96/1.66  tff(c_1034, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_1025])).
% 3.96/1.66  tff(c_255, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.96/1.66  tff(c_269, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_194, c_255])).
% 3.96/1.66  tff(c_493, plain, (![B_101, A_102]: (k1_relat_1(B_101)=A_102 | ~v1_partfun1(B_101, A_102) | ~v4_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.96/1.66  tff(c_496, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_269, c_493])).
% 3.96/1.66  tff(c_502, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_496])).
% 3.96/1.66  tff(c_512, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_502])).
% 3.96/1.66  tff(c_60, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.66  tff(c_110, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.96/1.66  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.66  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.66  tff(c_184, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_64])).
% 3.96/1.66  tff(c_193, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_184])).
% 3.96/1.66  tff(c_763, plain, (![B_131, C_132, A_133]: (k1_xboole_0=B_131 | v1_partfun1(C_132, A_133) | ~v1_funct_2(C_132, A_133, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_131))) | ~v1_funct_1(C_132))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.96/1.66  tff(c_766, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_194, c_763])).
% 3.96/1.66  tff(c_779, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_193, c_766])).
% 3.96/1.66  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_512, c_110, c_779])).
% 3.96/1.66  tff(c_782, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_502])).
% 3.96/1.66  tff(c_788, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_194])).
% 3.96/1.66  tff(c_1106, plain, (![A_150, B_151, C_152, D_153]: (k8_relset_1(A_150, B_151, C_152, D_153)=k10_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.96/1.66  tff(c_1116, plain, (![D_153]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_153)=k10_relat_1('#skF_3', D_153))), inference(resolution, [status(thm)], [c_788, c_1106])).
% 3.96/1.66  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.66  tff(c_218, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_182, c_58])).
% 3.96/1.66  tff(c_787, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_782, c_218])).
% 3.96/1.66  tff(c_1119, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_787])).
% 3.96/1.66  tff(c_1122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1119])).
% 3.96/1.66  tff(c_1124, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.96/1.66  tff(c_1197, plain, (![A_162]: (u1_struct_0(A_162)=k2_struct_0(A_162) | ~l1_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.96/1.66  tff(c_1200, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_1197])).
% 3.96/1.66  tff(c_1205, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1200])).
% 3.96/1.66  tff(c_1217, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1205, c_62])).
% 3.96/1.66  tff(c_1490, plain, (![A_210, B_211]: (k8_relset_1(A_210, A_210, k6_partfun1(A_210), B_211)=B_211 | ~m1_subset_1(B_211, k1_zfmisc_1(A_210)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.96/1.66  tff(c_1492, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1217, c_1490])).
% 3.96/1.66  tff(c_1496, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1492])).
% 3.96/1.66  tff(c_1831, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1827, c_1496])).
% 3.96/1.66  tff(c_1825, plain, (![A_229, B_230, D_232]: (k8_relset_1(A_229, B_230, k1_xboole_0, D_232)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1823])).
% 3.96/1.66  tff(c_1838, plain, (![A_229, B_230, D_232]: (k8_relset_1(A_229, B_230, '#skF_3', D_232)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_1831, c_1825])).
% 3.96/1.66  tff(c_1123, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.96/1.66  tff(c_1203, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_1197])).
% 3.96/1.66  tff(c_1207, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1203])).
% 3.96/1.66  tff(c_1242, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_1205, c_1124, c_1123, c_58])).
% 3.96/1.66  tff(c_1863, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_1831, c_1831, c_1831, c_1242])).
% 3.96/1.66  tff(c_2201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1838, c_1863])).
% 3.96/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.66  
% 3.96/1.66  Inference rules
% 3.96/1.66  ----------------------
% 3.96/1.66  #Ref     : 0
% 3.96/1.66  #Sup     : 474
% 3.96/1.66  #Fact    : 0
% 3.96/1.66  #Define  : 0
% 3.96/1.66  #Split   : 2
% 3.96/1.66  #Chain   : 0
% 3.96/1.66  #Close   : 0
% 3.96/1.66  
% 3.96/1.66  Ordering : KBO
% 3.96/1.66  
% 3.96/1.66  Simplification rules
% 3.96/1.66  ----------------------
% 3.96/1.66  #Subsume      : 31
% 3.96/1.66  #Demod        : 470
% 3.96/1.66  #Tautology    : 310
% 3.96/1.66  #SimpNegUnit  : 1
% 3.96/1.66  #BackRed      : 59
% 3.96/1.66  
% 3.96/1.66  #Partial instantiations: 0
% 3.96/1.66  #Strategies tried      : 1
% 3.96/1.66  
% 3.96/1.66  Timing (in seconds)
% 3.96/1.66  ----------------------
% 3.96/1.66  Preprocessing        : 0.34
% 3.96/1.67  Parsing              : 0.18
% 3.96/1.67  CNF conversion       : 0.02
% 3.96/1.67  Main loop            : 0.56
% 3.96/1.67  Inferencing          : 0.20
% 3.96/1.67  Reduction            : 0.20
% 3.96/1.67  Demodulation         : 0.14
% 3.96/1.67  BG Simplification    : 0.03
% 3.96/1.67  Subsumption          : 0.08
% 3.96/1.67  Abstraction          : 0.03
% 3.96/1.67  MUC search           : 0.00
% 3.96/1.67  Cooper               : 0.00
% 3.96/1.67  Total                : 0.94
% 3.96/1.67  Index Insertion      : 0.00
% 3.96/1.67  Index Deletion       : 0.00
% 3.96/1.67  Index Matching       : 0.00
% 3.96/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
