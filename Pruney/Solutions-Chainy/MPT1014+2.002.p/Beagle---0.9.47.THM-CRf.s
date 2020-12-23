%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:36 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 260 expanded)
%              Number of leaves         :   35 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 912 expanded)
%              Number of equality atoms :   49 ( 157 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_131,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),B)
                & k2_relset_1(A,A,B) = A )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_118,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_124,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_118])).

tff(c_76,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_109,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_117,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_109])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_249,plain,(
    ! [E_94,D_95,F_92,C_90,B_91,A_93] :
      ( k1_partfun1(A_93,B_91,C_90,D_95,E_94,F_92) = k5_relat_1(E_94,F_92)
      | ~ m1_subset_1(F_92,k1_zfmisc_1(k2_zfmisc_1(C_90,D_95)))
      | ~ v1_funct_1(F_92)
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_1(E_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_253,plain,(
    ! [A_93,B_91,E_94] :
      ( k1_partfun1(A_93,B_91,'#skF_1','#skF_1',E_94,'#skF_3') = k5_relat_1(E_94,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_1(E_94) ) ),
    inference(resolution,[status(thm)],[c_42,c_249])).

tff(c_273,plain,(
    ! [A_99,B_100,E_101] :
      ( k1_partfun1(A_99,B_100,'#skF_1','#skF_1',E_101,'#skF_3') = k5_relat_1(E_101,'#skF_3')
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(E_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_253])).

tff(c_276,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_273])).

tff(c_282,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_276])).

tff(c_40,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_160,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_166,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_40,c_160])).

tff(c_177,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_166])).

tff(c_207,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_287,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_207])).

tff(c_298,plain,(
    ! [E_104,C_102,B_103,A_106,F_105,D_107] :
      ( m1_subset_1(k1_partfun1(A_106,B_103,C_102,D_107,E_104,F_105),k1_zfmisc_1(k2_zfmisc_1(A_106,D_107)))
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_102,D_107)))
      | ~ v1_funct_1(F_105)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_103)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_328,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_298])).

tff(c_340,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_42,c_328])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_340])).

tff(c_343,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_395,plain,(
    ! [D_127,F_124,E_126,C_122,A_125,B_123] :
      ( k1_partfun1(A_125,B_123,C_122,D_127,E_126,F_124) = k5_relat_1(E_126,F_124)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_122,D_127)))
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_123)))
      | ~ v1_funct_1(E_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_399,plain,(
    ! [A_125,B_123,E_126] :
      ( k1_partfun1(A_125,B_123,'#skF_1','#skF_1',E_126,'#skF_3') = k5_relat_1(E_126,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_123)))
      | ~ v1_funct_1(E_126) ) ),
    inference(resolution,[status(thm)],[c_42,c_395])).

tff(c_429,plain,(
    ! [A_131,B_132,E_133] :
      ( k1_partfun1(A_131,B_132,'#skF_1','#skF_1',E_133,'#skF_3') = k5_relat_1(E_133,'#skF_3')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_399])).

tff(c_432,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_429])).

tff(c_438,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_343,c_432])).

tff(c_83,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_38,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_125,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_128,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_133,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_128])).

tff(c_178,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k2_relat_1(B_70),k1_relat_1(A_71))
      | k1_relat_1(k5_relat_1(B_70,A_71)) != k1_relat_1(B_70)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_186,plain,(
    ! [A_71] :
      ( r1_tarski('#skF_1',k1_relat_1(A_71))
      | k1_relat_1(k5_relat_1('#skF_2',A_71)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_178])).

tff(c_191,plain,(
    ! [A_72] :
      ( r1_tarski('#skF_1',k1_relat_1(A_72))
      | k1_relat_1(k5_relat_1('#skF_2',A_72)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_52,c_186])).

tff(c_85,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k1_relat_1(B_45),A_46)
      | ~ v4_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [B_45,A_46] :
      ( k1_relat_1(B_45) = A_46
      | ~ r1_tarski(A_46,k1_relat_1(B_45))
      | ~ v4_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_197,plain,(
    ! [A_72] :
      ( k1_relat_1(A_72) = '#skF_1'
      | ~ v4_relat_1(A_72,'#skF_1')
      | k1_relat_1(k5_relat_1('#skF_2',A_72)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_191,c_88])).

tff(c_445,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_197])).

tff(c_452,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46,c_117,c_445])).

tff(c_34,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_14,plain,(
    ! [B_10,A_8] :
      ( k6_relat_1(k1_relat_1(B_10)) = B_10
      | k5_relat_1(A_8,B_10) != A_8
      | k2_relat_1(A_8) != k1_relat_1(B_10)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_53,plain,(
    ! [B_10,A_8] :
      ( k6_partfun1(k1_relat_1(B_10)) = B_10
      | k5_relat_1(A_8,B_10) != A_8
      | k2_relat_1(A_8) != k1_relat_1(B_10)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_447,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_53])).

tff(c_455,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_52,c_84,c_46,c_133,c_447])).

tff(c_589,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_455])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_590,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_36])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.43  
% 2.78/1.43  %Foreground sorts:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Background operators:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Foreground operators:
% 2.78/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.78/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.43  
% 2.78/1.45  tff(f_131, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_funct_2)).
% 2.78/1.45  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.78/1.45  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.78/1.45  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.78/1.45  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.78/1.45  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.78/1.45  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.78/1.45  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 2.78/1.45  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.78/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.45  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.78/1.45  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 2.78/1.45  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.45  tff(c_118, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.45  tff(c_124, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_118])).
% 2.78/1.45  tff(c_76, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.45  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_76])).
% 2.78/1.45  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.45  tff(c_109, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.45  tff(c_117, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_109])).
% 2.78/1.45  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.45  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.45  tff(c_249, plain, (![E_94, D_95, F_92, C_90, B_91, A_93]: (k1_partfun1(A_93, B_91, C_90, D_95, E_94, F_92)=k5_relat_1(E_94, F_92) | ~m1_subset_1(F_92, k1_zfmisc_1(k2_zfmisc_1(C_90, D_95))) | ~v1_funct_1(F_92) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_1(E_94))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.45  tff(c_253, plain, (![A_93, B_91, E_94]: (k1_partfun1(A_93, B_91, '#skF_1', '#skF_1', E_94, '#skF_3')=k5_relat_1(E_94, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_1(E_94))), inference(resolution, [status(thm)], [c_42, c_249])).
% 2.78/1.45  tff(c_273, plain, (![A_99, B_100, E_101]: (k1_partfun1(A_99, B_100, '#skF_1', '#skF_1', E_101, '#skF_3')=k5_relat_1(E_101, '#skF_3') | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(E_101))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_253])).
% 2.78/1.45  tff(c_276, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_273])).
% 2.78/1.45  tff(c_282, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_276])).
% 2.78/1.45  tff(c_40, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.45  tff(c_160, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.45  tff(c_166, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_40, c_160])).
% 2.78/1.45  tff(c_177, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_166])).
% 2.78/1.45  tff(c_207, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_177])).
% 2.78/1.45  tff(c_287, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_207])).
% 2.78/1.45  tff(c_298, plain, (![E_104, C_102, B_103, A_106, F_105, D_107]: (m1_subset_1(k1_partfun1(A_106, B_103, C_102, D_107, E_104, F_105), k1_zfmisc_1(k2_zfmisc_1(A_106, D_107))) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_102, D_107))) | ~v1_funct_1(F_105) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_103))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.45  tff(c_328, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_282, c_298])).
% 2.78/1.45  tff(c_340, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_42, c_328])).
% 2.78/1.45  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_340])).
% 2.78/1.45  tff(c_343, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_177])).
% 2.78/1.45  tff(c_395, plain, (![D_127, F_124, E_126, C_122, A_125, B_123]: (k1_partfun1(A_125, B_123, C_122, D_127, E_126, F_124)=k5_relat_1(E_126, F_124) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_122, D_127))) | ~v1_funct_1(F_124) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_123))) | ~v1_funct_1(E_126))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.45  tff(c_399, plain, (![A_125, B_123, E_126]: (k1_partfun1(A_125, B_123, '#skF_1', '#skF_1', E_126, '#skF_3')=k5_relat_1(E_126, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_123))) | ~v1_funct_1(E_126))), inference(resolution, [status(thm)], [c_42, c_395])).
% 2.78/1.45  tff(c_429, plain, (![A_131, B_132, E_133]: (k1_partfun1(A_131, B_132, '#skF_1', '#skF_1', E_133, '#skF_3')=k5_relat_1(E_133, '#skF_3') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(E_133))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_399])).
% 2.78/1.45  tff(c_432, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_429])).
% 2.78/1.45  tff(c_438, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_343, c_432])).
% 2.78/1.45  tff(c_83, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_76])).
% 2.78/1.45  tff(c_38, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.45  tff(c_125, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.78/1.45  tff(c_128, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_125])).
% 2.78/1.45  tff(c_133, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_128])).
% 2.78/1.45  tff(c_178, plain, (![B_70, A_71]: (r1_tarski(k2_relat_1(B_70), k1_relat_1(A_71)) | k1_relat_1(k5_relat_1(B_70, A_71))!=k1_relat_1(B_70) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.78/1.45  tff(c_186, plain, (![A_71]: (r1_tarski('#skF_1', k1_relat_1(A_71)) | k1_relat_1(k5_relat_1('#skF_2', A_71))!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_133, c_178])).
% 2.78/1.45  tff(c_191, plain, (![A_72]: (r1_tarski('#skF_1', k1_relat_1(A_72)) | k1_relat_1(k5_relat_1('#skF_2', A_72))!=k1_relat_1('#skF_2') | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_52, c_186])).
% 2.78/1.45  tff(c_85, plain, (![B_45, A_46]: (r1_tarski(k1_relat_1(B_45), A_46) | ~v4_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.45  tff(c_88, plain, (![B_45, A_46]: (k1_relat_1(B_45)=A_46 | ~r1_tarski(A_46, k1_relat_1(B_45)) | ~v4_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_85, c_2])).
% 2.78/1.45  tff(c_197, plain, (![A_72]: (k1_relat_1(A_72)='#skF_1' | ~v4_relat_1(A_72, '#skF_1') | k1_relat_1(k5_relat_1('#skF_2', A_72))!=k1_relat_1('#skF_2') | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_191, c_88])).
% 2.78/1.45  tff(c_445, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_438, c_197])).
% 2.78/1.45  tff(c_452, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46, c_117, c_445])).
% 2.78/1.45  tff(c_34, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.78/1.45  tff(c_14, plain, (![B_10, A_8]: (k6_relat_1(k1_relat_1(B_10))=B_10 | k5_relat_1(A_8, B_10)!=A_8 | k2_relat_1(A_8)!=k1_relat_1(B_10) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.78/1.45  tff(c_53, plain, (![B_10, A_8]: (k6_partfun1(k1_relat_1(B_10))=B_10 | k5_relat_1(A_8, B_10)!=A_8 | k2_relat_1(A_8)!=k1_relat_1(B_10) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 2.78/1.45  tff(c_447, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_438, c_53])).
% 2.78/1.45  tff(c_455, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_52, c_84, c_46, c_133, c_447])).
% 2.78/1.45  tff(c_589, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_455])).
% 2.78/1.45  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.45  tff(c_590, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_36])).
% 2.78/1.45  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_590])).
% 2.78/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  Inference rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Ref     : 0
% 2.78/1.45  #Sup     : 113
% 2.78/1.45  #Fact    : 0
% 2.78/1.45  #Define  : 0
% 2.78/1.45  #Split   : 1
% 2.78/1.45  #Chain   : 0
% 2.78/1.45  #Close   : 0
% 2.78/1.45  
% 2.78/1.45  Ordering : KBO
% 2.78/1.45  
% 2.78/1.45  Simplification rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Subsume      : 6
% 2.78/1.45  #Demod        : 111
% 2.78/1.45  #Tautology    : 37
% 2.78/1.45  #SimpNegUnit  : 1
% 2.78/1.45  #BackRed      : 7
% 2.78/1.45  
% 2.78/1.45  #Partial instantiations: 0
% 2.78/1.45  #Strategies tried      : 1
% 2.78/1.45  
% 2.78/1.45  Timing (in seconds)
% 2.78/1.45  ----------------------
% 2.78/1.45  Preprocessing        : 0.35
% 2.78/1.45  Parsing              : 0.19
% 2.78/1.45  CNF conversion       : 0.02
% 2.78/1.45  Main loop            : 0.33
% 2.78/1.45  Inferencing          : 0.12
% 2.78/1.45  Reduction            : 0.10
% 2.78/1.45  Demodulation         : 0.07
% 2.78/1.45  BG Simplification    : 0.02
% 2.78/1.45  Subsumption          : 0.06
% 2.78/1.45  Abstraction          : 0.02
% 2.78/1.45  MUC search           : 0.00
% 2.78/1.45  Cooper               : 0.00
% 2.78/1.45  Total                : 0.71
% 2.78/1.45  Index Insertion      : 0.00
% 2.78/1.45  Index Deletion       : 0.00
% 2.78/1.45  Index Matching       : 0.00
% 2.78/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
