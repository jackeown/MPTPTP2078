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
% DateTime   : Thu Dec  3 10:23:41 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  154 (22258 expanded)
%              Number of leaves         :   42 (7749 expanded)
%              Depth                    :   26
%              Number of atoms          :  407 (63769 expanded)
%              Number of equality atoms :   72 (13793 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_66,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_74,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_66])).

tff(c_60,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_73,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_66])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_73,c_54])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_101])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_84,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(u1_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_90,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_84])).

tff(c_94,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_90])).

tff(c_95,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_94])).

tff(c_110,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_114,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_98,c_110])).

tff(c_178,plain,(
    ! [B_56,A_57] :
      ( k1_relat_1(B_56) = A_57
      | ~ v1_partfun1(B_56,A_57)
      | ~ v4_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_181,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_178])).

tff(c_184,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_181])).

tff(c_185,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_83,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_73,c_56])).

tff(c_196,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_partfun1(C_61,A_62)
      | ~ v1_funct_2(C_61,A_62,B_63)
      | ~ v1_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | v1_xboole_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_199,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_98,c_196])).

tff(c_202,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_83,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_185,c_202])).

tff(c_205,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_210,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_98])).

tff(c_261,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_265,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_210,c_261])).

tff(c_52,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_105,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_73,c_52])).

tff(c_209,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_105])).

tff(c_274,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_209])).

tff(c_212,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_83])).

tff(c_281,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_212])).

tff(c_280,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_210])).

tff(c_331,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_funct_2(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(D_72,A_70,B_71)
      | ~ v1_funct_1(D_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_333,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_331])).

tff(c_336,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_333])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_279,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_265])).

tff(c_348,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_funct_1(k2_funct_1(C_74))
      | k2_relset_1(A_75,B_76,C_74) != B_76
      | ~ v2_funct_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_2(C_74,A_75,B_76)
      | ~ v1_funct_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_351,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_348])).

tff(c_354,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_50,c_279,c_351])).

tff(c_355,plain,(
    ! [C_77,B_78,A_79] :
      ( v1_funct_2(k2_funct_1(C_77),B_78,A_79)
      | k2_relset_1(A_79,B_78,C_77) != B_78
      | ~ v2_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_2(C_77,A_79,B_78)
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_358,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_355])).

tff(c_361,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_50,c_279,c_358])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_369,plain,(
    ! [C_83,B_84,A_85] :
      ( m1_subset_1(k2_funct_1(C_83),k1_zfmisc_1(k2_zfmisc_1(B_84,A_85)))
      | k2_relset_1(A_85,B_84,C_83) != B_84
      | ~ v2_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84)))
      | ~ v1_funct_2(C_83,A_85,B_84)
      | ~ v1_funct_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_395,plain,(
    ! [C_83,B_84,A_85] :
      ( v1_relat_1(k2_funct_1(C_83))
      | ~ v1_relat_1(k2_zfmisc_1(B_84,A_85))
      | k2_relset_1(A_85,B_84,C_83) != B_84
      | ~ v2_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84)))
      | ~ v1_funct_2(C_83,A_85,B_84)
      | ~ v1_funct_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_369,c_2])).

tff(c_415,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_relat_1(k2_funct_1(C_86))
      | k2_relset_1(A_87,B_88,C_86) != B_88
      | ~ v2_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_2(C_86,A_87,B_88)
      | ~ v1_funct_1(C_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_395])).

tff(c_421,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_415])).

tff(c_425,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_50,c_279,c_421])).

tff(c_20,plain,(
    ! [C_11,A_9,B_10] :
      ( v4_relat_1(C_11,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_426,plain,(
    ! [C_89,B_90,A_91] :
      ( v4_relat_1(k2_funct_1(C_89),B_90)
      | k2_relset_1(A_91,B_90,C_89) != B_90
      | ~ v2_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90)))
      | ~ v1_funct_2(C_89,A_91,B_90)
      | ~ v1_funct_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_369,c_20])).

tff(c_432,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_426])).

tff(c_436,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_50,c_279,c_432])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(B_20) = A_19
      | ~ v1_partfun1(B_20,A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_439,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_436,c_30])).

tff(c_442,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_439])).

tff(c_443,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_163,plain,(
    ! [A_55] :
      ( k1_relat_1(k2_funct_1(A_55)) = k2_relat_1(A_55)
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [B_20] :
      ( v1_partfun1(B_20,k1_relat_1(B_20))
      | ~ v4_relat_1(B_20,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_338,plain,(
    ! [A_73] :
      ( v1_partfun1(k2_funct_1(A_73),k1_relat_1(k2_funct_1(A_73)))
      | ~ v4_relat_1(k2_funct_1(A_73),k2_relat_1(A_73))
      | ~ v1_relat_1(k2_funct_1(A_73))
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_28])).

tff(c_462,plain,(
    ! [A_99] :
      ( v1_partfun1(k2_funct_1(A_99),k2_relat_1(A_99))
      | ~ v4_relat_1(k2_funct_1(A_99),k2_relat_1(A_99))
      | ~ v1_relat_1(k2_funct_1(A_99))
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99)
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_338])).

tff(c_465,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_462])).

tff(c_474,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58,c_50,c_425,c_465])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_443,c_474])).

tff(c_477,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_566,plain,(
    ! [A_112] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_112)),k1_relat_1(A_112))
      | ~ v4_relat_1(k2_funct_1(k2_funct_1(A_112)),k2_relat_1(k2_funct_1(A_112)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_112)))
      | ~ v2_funct_1(k2_funct_1(A_112))
      | ~ v1_funct_1(k2_funct_1(A_112))
      | ~ v1_relat_1(k2_funct_1(A_112))
      | ~ v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_338])).

tff(c_610,plain,(
    ! [A_122] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_122)),k1_relat_1(A_122))
      | ~ v4_relat_1(A_122,k2_relat_1(k2_funct_1(A_122)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_122)))
      | ~ v2_funct_1(k2_funct_1(A_122))
      | ~ v1_funct_1(k2_funct_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122)
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_566])).

tff(c_613,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_610])).

tff(c_624,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_354,c_425,c_354,c_613])).

tff(c_625,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_639,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_625])).

tff(c_643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58,c_50,c_639])).

tff(c_645,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_538,plain,(
    ! [B_108,A_109,C_110] :
      ( k2_relset_1(B_108,A_109,k2_funct_1(C_110)) = k2_relat_1(k2_funct_1(C_110))
      | k2_relset_1(A_109,B_108,C_110) != B_108
      | ~ v2_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_2(C_110,A_109,B_108)
      | ~ v1_funct_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_369,c_22])).

tff(c_544,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_538])).

tff(c_548,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_50,c_279,c_544])).

tff(c_40,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_funct_1(k2_funct_1(C_27))
      | k2_relset_1(A_25,B_26,C_27) != B_26
      | ~ v2_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_723,plain,(
    ! [C_126,B_127,A_128] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_126)))
      | k2_relset_1(B_127,A_128,k2_funct_1(C_126)) != A_128
      | ~ v2_funct_1(k2_funct_1(C_126))
      | ~ v1_funct_2(k2_funct_1(C_126),B_127,A_128)
      | ~ v1_funct_1(k2_funct_1(C_126))
      | k2_relset_1(A_128,B_127,C_126) != B_127
      | ~ v2_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_2(C_126,A_128,B_127)
      | ~ v1_funct_1(C_126) ) ),
    inference(resolution,[status(thm)],[c_369,c_40])).

tff(c_729,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_723])).

tff(c_733,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_50,c_279,c_354,c_361,c_645,c_548,c_729])).

tff(c_734,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_733])).

tff(c_737,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_734])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58,c_50,c_737])).

tff(c_743,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_749,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_548])).

tff(c_46,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_tops_2(A_30,B_31,C_32) = k2_funct_1(C_32)
      | ~ v2_funct_1(C_32)
      | k2_relset_1(A_30,B_31,C_32) != B_31
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_991,plain,(
    ! [B_135,A_136,C_137] :
      ( k2_tops_2(B_135,A_136,k2_funct_1(C_137)) = k2_funct_1(k2_funct_1(C_137))
      | ~ v2_funct_1(k2_funct_1(C_137))
      | k2_relset_1(B_135,A_136,k2_funct_1(C_137)) != A_136
      | ~ v1_funct_2(k2_funct_1(C_137),B_135,A_136)
      | ~ v1_funct_1(k2_funct_1(C_137))
      | k2_relset_1(A_136,B_135,C_137) != B_135
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135)))
      | ~ v1_funct_2(C_137,A_136,B_135)
      | ~ v1_funct_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_369,c_46])).

tff(c_997,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_991])).

tff(c_1001,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_50,c_279,c_354,c_361,c_749,c_645,c_997])).

tff(c_362,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_tops_2(A_80,B_81,C_82) = k2_funct_1(C_82)
      | ~ v2_funct_1(C_82)
      | k2_relset_1(A_80,B_81,C_82) != B_81
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_365,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_362])).

tff(c_368,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_281,c_279,c_50,c_365])).

tff(c_48,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_115,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_74,c_73,c_73,c_73,c_48])).

tff(c_208,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_205,c_205,c_115])).

tff(c_337,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_274,c_208])).

tff(c_410,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_337])).

tff(c_1049,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_410])).

tff(c_1056,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1049])).

tff(c_1059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58,c_50,c_336,c_1056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.60  
% 3.55/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.60  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.55/1.60  
% 3.55/1.60  %Foreground sorts:
% 3.55/1.60  
% 3.55/1.60  
% 3.55/1.60  %Background operators:
% 3.55/1.60  
% 3.55/1.60  
% 3.55/1.60  %Foreground operators:
% 3.55/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.55/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.55/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.55/1.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.55/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.60  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.55/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.55/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.55/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.55/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.55/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.55/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.60  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.55/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.60  
% 3.55/1.63  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.55/1.63  tff(f_174, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.55/1.63  tff(f_132, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.55/1.63  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.55/1.63  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.55/1.63  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.55/1.63  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.55/1.63  tff(f_88, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.55/1.63  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.55/1.63  tff(f_112, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.55/1.63  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.55/1.63  tff(f_128, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.55/1.63  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.55/1.63  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.55/1.63  tff(f_152, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.55/1.63  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.55/1.63  tff(c_64, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_66, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.55/1.63  tff(c_74, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_66])).
% 3.55/1.63  tff(c_60, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_73, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_66])).
% 3.55/1.63  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_73, c_54])).
% 3.55/1.63  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.63  tff(c_101, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_98, c_2])).
% 3.55/1.63  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_101])).
% 3.55/1.63  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_84, plain, (![A_40]: (~v1_xboole_0(u1_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.55/1.63  tff(c_90, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73, c_84])).
% 3.55/1.63  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_90])).
% 3.55/1.63  tff(c_95, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_94])).
% 3.55/1.63  tff(c_110, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.55/1.63  tff(c_114, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_98, c_110])).
% 3.55/1.63  tff(c_178, plain, (![B_56, A_57]: (k1_relat_1(B_56)=A_57 | ~v1_partfun1(B_56, A_57) | ~v4_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.55/1.63  tff(c_181, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_178])).
% 3.55/1.63  tff(c_184, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_181])).
% 3.55/1.63  tff(c_185, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_184])).
% 3.55/1.63  tff(c_56, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_83, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_73, c_56])).
% 3.55/1.63  tff(c_196, plain, (![C_61, A_62, B_63]: (v1_partfun1(C_61, A_62) | ~v1_funct_2(C_61, A_62, B_63) | ~v1_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | v1_xboole_0(B_63))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.55/1.63  tff(c_199, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_98, c_196])).
% 3.55/1.63  tff(c_202, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_83, c_199])).
% 3.55/1.63  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_185, c_202])).
% 3.55/1.63  tff(c_205, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_184])).
% 3.55/1.63  tff(c_210, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_98])).
% 3.55/1.63  tff(c_261, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.55/1.63  tff(c_265, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_210, c_261])).
% 3.55/1.63  tff(c_52, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_105, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_73, c_52])).
% 3.55/1.63  tff(c_209, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_105])).
% 3.55/1.63  tff(c_274, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_209])).
% 3.55/1.63  tff(c_212, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_83])).
% 3.55/1.63  tff(c_281, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_212])).
% 3.55/1.63  tff(c_280, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_210])).
% 3.55/1.63  tff(c_331, plain, (![A_70, B_71, D_72]: (r2_funct_2(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(D_72, A_70, B_71) | ~v1_funct_1(D_72))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.55/1.63  tff(c_333, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_331])).
% 3.55/1.63  tff(c_336, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_333])).
% 3.55/1.63  tff(c_16, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.63  tff(c_279, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_265])).
% 3.55/1.63  tff(c_348, plain, (![C_74, A_75, B_76]: (v1_funct_1(k2_funct_1(C_74)) | k2_relset_1(A_75, B_76, C_74)!=B_76 | ~v2_funct_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_2(C_74, A_75, B_76) | ~v1_funct_1(C_74))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.55/1.63  tff(c_351, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_348])).
% 3.55/1.63  tff(c_354, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_50, c_279, c_351])).
% 3.55/1.63  tff(c_355, plain, (![C_77, B_78, A_79]: (v1_funct_2(k2_funct_1(C_77), B_78, A_79) | k2_relset_1(A_79, B_78, C_77)!=B_78 | ~v2_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_2(C_77, A_79, B_78) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.55/1.63  tff(c_358, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_355])).
% 3.55/1.63  tff(c_361, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_50, c_279, c_358])).
% 3.55/1.63  tff(c_12, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.63  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.63  tff(c_369, plain, (![C_83, B_84, A_85]: (m1_subset_1(k2_funct_1(C_83), k1_zfmisc_1(k2_zfmisc_1(B_84, A_85))) | k2_relset_1(A_85, B_84, C_83)!=B_84 | ~v2_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))) | ~v1_funct_2(C_83, A_85, B_84) | ~v1_funct_1(C_83))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.55/1.63  tff(c_395, plain, (![C_83, B_84, A_85]: (v1_relat_1(k2_funct_1(C_83)) | ~v1_relat_1(k2_zfmisc_1(B_84, A_85)) | k2_relset_1(A_85, B_84, C_83)!=B_84 | ~v2_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))) | ~v1_funct_2(C_83, A_85, B_84) | ~v1_funct_1(C_83))), inference(resolution, [status(thm)], [c_369, c_2])).
% 3.55/1.63  tff(c_415, plain, (![C_86, A_87, B_88]: (v1_relat_1(k2_funct_1(C_86)) | k2_relset_1(A_87, B_88, C_86)!=B_88 | ~v2_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_2(C_86, A_87, B_88) | ~v1_funct_1(C_86))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_395])).
% 3.55/1.63  tff(c_421, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_415])).
% 3.55/1.63  tff(c_425, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_50, c_279, c_421])).
% 3.55/1.63  tff(c_20, plain, (![C_11, A_9, B_10]: (v4_relat_1(C_11, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.55/1.63  tff(c_426, plain, (![C_89, B_90, A_91]: (v4_relat_1(k2_funct_1(C_89), B_90) | k2_relset_1(A_91, B_90, C_89)!=B_90 | ~v2_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))) | ~v1_funct_2(C_89, A_91, B_90) | ~v1_funct_1(C_89))), inference(resolution, [status(thm)], [c_369, c_20])).
% 3.55/1.63  tff(c_432, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_426])).
% 3.55/1.63  tff(c_436, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_50, c_279, c_432])).
% 3.55/1.63  tff(c_30, plain, (![B_20, A_19]: (k1_relat_1(B_20)=A_19 | ~v1_partfun1(B_20, A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.55/1.63  tff(c_439, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_436, c_30])).
% 3.55/1.63  tff(c_442, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_439])).
% 3.55/1.63  tff(c_443, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_442])).
% 3.55/1.63  tff(c_14, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.63  tff(c_163, plain, (![A_55]: (k1_relat_1(k2_funct_1(A_55))=k2_relat_1(A_55) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.63  tff(c_28, plain, (![B_20]: (v1_partfun1(B_20, k1_relat_1(B_20)) | ~v4_relat_1(B_20, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.55/1.63  tff(c_338, plain, (![A_73]: (v1_partfun1(k2_funct_1(A_73), k1_relat_1(k2_funct_1(A_73))) | ~v4_relat_1(k2_funct_1(A_73), k2_relat_1(A_73)) | ~v1_relat_1(k2_funct_1(A_73)) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_163, c_28])).
% 3.55/1.63  tff(c_462, plain, (![A_99]: (v1_partfun1(k2_funct_1(A_99), k2_relat_1(A_99)) | ~v4_relat_1(k2_funct_1(A_99), k2_relat_1(A_99)) | ~v1_relat_1(k2_funct_1(A_99)) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_14, c_338])).
% 3.55/1.63  tff(c_465, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_462])).
% 3.55/1.63  tff(c_474, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_58, c_50, c_425, c_465])).
% 3.55/1.63  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_443, c_474])).
% 3.55/1.63  tff(c_477, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_442])).
% 3.55/1.63  tff(c_566, plain, (![A_112]: (v1_partfun1(k2_funct_1(k2_funct_1(A_112)), k1_relat_1(A_112)) | ~v4_relat_1(k2_funct_1(k2_funct_1(A_112)), k2_relat_1(k2_funct_1(A_112))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_112))) | ~v2_funct_1(k2_funct_1(A_112)) | ~v1_funct_1(k2_funct_1(A_112)) | ~v1_relat_1(k2_funct_1(A_112)) | ~v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_16, c_338])).
% 3.55/1.63  tff(c_610, plain, (![A_122]: (v1_partfun1(k2_funct_1(k2_funct_1(A_122)), k1_relat_1(A_122)) | ~v4_relat_1(A_122, k2_relat_1(k2_funct_1(A_122))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_122))) | ~v2_funct_1(k2_funct_1(A_122)) | ~v1_funct_1(k2_funct_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_16, c_566])).
% 3.55/1.63  tff(c_613, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_610])).
% 3.55/1.63  tff(c_624, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_354, c_425, c_354, c_613])).
% 3.55/1.63  tff(c_625, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_624])).
% 3.55/1.63  tff(c_639, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_625])).
% 3.55/1.63  tff(c_643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_58, c_50, c_639])).
% 3.55/1.63  tff(c_645, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_624])).
% 3.55/1.63  tff(c_22, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.55/1.63  tff(c_538, plain, (![B_108, A_109, C_110]: (k2_relset_1(B_108, A_109, k2_funct_1(C_110))=k2_relat_1(k2_funct_1(C_110)) | k2_relset_1(A_109, B_108, C_110)!=B_108 | ~v2_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_2(C_110, A_109, B_108) | ~v1_funct_1(C_110))), inference(resolution, [status(thm)], [c_369, c_22])).
% 3.55/1.63  tff(c_544, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_538])).
% 3.55/1.63  tff(c_548, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_50, c_279, c_544])).
% 3.55/1.63  tff(c_40, plain, (![C_27, A_25, B_26]: (v1_funct_1(k2_funct_1(C_27)) | k2_relset_1(A_25, B_26, C_27)!=B_26 | ~v2_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.55/1.63  tff(c_723, plain, (![C_126, B_127, A_128]: (v1_funct_1(k2_funct_1(k2_funct_1(C_126))) | k2_relset_1(B_127, A_128, k2_funct_1(C_126))!=A_128 | ~v2_funct_1(k2_funct_1(C_126)) | ~v1_funct_2(k2_funct_1(C_126), B_127, A_128) | ~v1_funct_1(k2_funct_1(C_126)) | k2_relset_1(A_128, B_127, C_126)!=B_127 | ~v2_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_2(C_126, A_128, B_127) | ~v1_funct_1(C_126))), inference(resolution, [status(thm)], [c_369, c_40])).
% 3.55/1.63  tff(c_729, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_723])).
% 3.55/1.63  tff(c_733, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_50, c_279, c_354, c_361, c_645, c_548, c_729])).
% 3.55/1.63  tff(c_734, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_733])).
% 3.55/1.63  tff(c_737, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_734])).
% 3.55/1.63  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_58, c_50, c_737])).
% 3.55/1.63  tff(c_743, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_733])).
% 3.55/1.63  tff(c_749, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_743, c_548])).
% 3.55/1.63  tff(c_46, plain, (![A_30, B_31, C_32]: (k2_tops_2(A_30, B_31, C_32)=k2_funct_1(C_32) | ~v2_funct_1(C_32) | k2_relset_1(A_30, B_31, C_32)!=B_31 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.55/1.63  tff(c_991, plain, (![B_135, A_136, C_137]: (k2_tops_2(B_135, A_136, k2_funct_1(C_137))=k2_funct_1(k2_funct_1(C_137)) | ~v2_funct_1(k2_funct_1(C_137)) | k2_relset_1(B_135, A_136, k2_funct_1(C_137))!=A_136 | ~v1_funct_2(k2_funct_1(C_137), B_135, A_136) | ~v1_funct_1(k2_funct_1(C_137)) | k2_relset_1(A_136, B_135, C_137)!=B_135 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))) | ~v1_funct_2(C_137, A_136, B_135) | ~v1_funct_1(C_137))), inference(resolution, [status(thm)], [c_369, c_46])).
% 3.55/1.63  tff(c_997, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_991])).
% 3.55/1.63  tff(c_1001, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_50, c_279, c_354, c_361, c_749, c_645, c_997])).
% 3.55/1.63  tff(c_362, plain, (![A_80, B_81, C_82]: (k2_tops_2(A_80, B_81, C_82)=k2_funct_1(C_82) | ~v2_funct_1(C_82) | k2_relset_1(A_80, B_81, C_82)!=B_81 | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_82, A_80, B_81) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.55/1.63  tff(c_365, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_362])).
% 3.55/1.63  tff(c_368, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_281, c_279, c_50, c_365])).
% 3.55/1.63  tff(c_48, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.55/1.63  tff(c_115, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_74, c_73, c_73, c_73, c_48])).
% 3.55/1.63  tff(c_208, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_205, c_205, c_115])).
% 3.55/1.63  tff(c_337, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_274, c_208])).
% 3.55/1.63  tff(c_410, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_337])).
% 3.55/1.63  tff(c_1049, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_410])).
% 3.55/1.63  tff(c_1056, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1049])).
% 3.55/1.63  tff(c_1059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_58, c_50, c_336, c_1056])).
% 3.55/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.63  
% 3.55/1.63  Inference rules
% 3.55/1.63  ----------------------
% 3.55/1.63  #Ref     : 0
% 3.55/1.63  #Sup     : 210
% 3.55/1.63  #Fact    : 0
% 3.55/1.63  #Define  : 0
% 3.55/1.63  #Split   : 13
% 3.55/1.63  #Chain   : 0
% 3.55/1.63  #Close   : 0
% 3.55/1.63  
% 3.55/1.63  Ordering : KBO
% 3.55/1.63  
% 3.55/1.63  Simplification rules
% 3.55/1.63  ----------------------
% 3.55/1.63  #Subsume      : 4
% 3.55/1.63  #Demod        : 396
% 3.55/1.63  #Tautology    : 110
% 3.55/1.63  #SimpNegUnit  : 7
% 3.55/1.63  #BackRed      : 20
% 3.55/1.63  
% 3.55/1.63  #Partial instantiations: 0
% 3.55/1.63  #Strategies tried      : 1
% 3.55/1.63  
% 3.55/1.63  Timing (in seconds)
% 3.55/1.63  ----------------------
% 3.55/1.63  Preprocessing        : 0.36
% 3.55/1.63  Parsing              : 0.19
% 3.55/1.63  CNF conversion       : 0.02
% 3.55/1.63  Main loop            : 0.45
% 3.55/1.63  Inferencing          : 0.15
% 3.55/1.63  Reduction            : 0.15
% 3.55/1.63  Demodulation         : 0.11
% 3.55/1.63  BG Simplification    : 0.03
% 3.55/1.63  Subsumption          : 0.08
% 3.55/1.63  Abstraction          : 0.02
% 3.55/1.63  MUC search           : 0.00
% 3.55/1.63  Cooper               : 0.00
% 3.55/1.63  Total                : 0.86
% 3.55/1.63  Index Insertion      : 0.00
% 3.55/1.63  Index Deletion       : 0.00
% 3.55/1.63  Index Matching       : 0.00
% 3.55/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
