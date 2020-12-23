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
% DateTime   : Thu Dec  3 10:23:39 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  183 (94027 expanded)
%              Number of leaves         :   53 (32721 expanded)
%              Depth                    :   30
%              Number of atoms          :  422 (267595 expanded)
%              Number of equality atoms :  101 (57689 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_229,negated_conjecture,(
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

tff(f_187,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_195,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_157,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_173,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_183,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_207,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_82,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_84,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_92,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_84])).

tff(c_78,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_91,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_84])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_122,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_91,c_72])).

tff(c_232,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_240,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_232])).

tff(c_70,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_117,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_91,c_70])).

tff(c_242,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_117])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_102,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(u1_struct_0(A_53))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_108,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_102])).

tff(c_112,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_108])).

tff(c_113,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_112])).

tff(c_251,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_113])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_123,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_122,c_123])).

tff(c_129,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_159,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_163,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_122,c_159])).

tff(c_188,plain,(
    ! [B_72,A_73] :
      ( k1_relat_1(B_72) = A_73
      | ~ v1_partfun1(B_72,A_73)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_191,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_163,c_188])).

tff(c_194,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_191])).

tff(c_195,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_74,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_101,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_91,c_74])).

tff(c_252,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_101])).

tff(c_250,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_122])).

tff(c_378,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_partfun1(C_90,A_91)
      | ~ v1_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | v1_xboole_0(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_381,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_250,c_378])).

tff(c_387,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_252,c_381])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_195,c_387])).

tff(c_390,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_396,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_122])).

tff(c_36,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_relset_1(A_24,B_25,C_26) = k2_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_461,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_396,c_36])).

tff(c_397,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_117])).

tff(c_474,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_397])).

tff(c_399,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_101])).

tff(c_481,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_399])).

tff(c_480,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_396])).

tff(c_1199,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( r2_funct_2(A_145,B_146,C_147,C_147)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_2(D_148,A_145,B_146)
      | ~ v1_funct_1(D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_2(C_147,A_145,B_146)
      | ~ v1_funct_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1205,plain,(
    ! [C_147] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_147,C_147)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_147,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_480,c_1199])).

tff(c_1278,plain,(
    ! [C_149] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_149,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_149,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_481,c_1205])).

tff(c_1283,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_480,c_1278])).

tff(c_1290,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_481,c_1283])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_28,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k2_funct_1(A_17)) = k6_relat_1(k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_479,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_461])).

tff(c_716,plain,(
    ! [C_113,A_114,B_115] :
      ( v1_funct_1(k2_funct_1(C_113))
      | k2_relset_1(A_114,B_115,C_113) != B_115
      | ~ v2_funct_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_2(C_113,A_114,B_115)
      | ~ v1_funct_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_719,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_480,c_716])).

tff(c_725,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_481,c_68,c_479,c_719])).

tff(c_961,plain,(
    ! [C_130,B_131,A_132] :
      ( v1_funct_2(k2_funct_1(C_130),B_131,A_132)
      | k2_relset_1(A_132,B_131,C_130) != B_131
      | ~ v2_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(C_130,A_132,B_131)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_967,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_480,c_961])).

tff(c_974,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_481,c_68,c_479,c_967])).

tff(c_996,plain,(
    ! [C_136,B_137,A_138] :
      ( m1_subset_1(k2_funct_1(C_136),k1_zfmisc_1(k2_zfmisc_1(B_137,A_138)))
      | k2_relset_1(A_138,B_137,C_136) != B_137
      | ~ v2_funct_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_2(C_136,A_138,B_137)
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1020,plain,(
    ! [C_136,B_137,A_138] :
      ( v1_relat_1(k2_funct_1(C_136))
      | ~ v1_relat_1(k2_zfmisc_1(B_137,A_138))
      | k2_relset_1(A_138,B_137,C_136) != B_137
      | ~ v2_funct_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_2(C_136,A_138,B_137)
      | ~ v1_funct_1(C_136) ) ),
    inference(resolution,[status(thm)],[c_996,c_2])).

tff(c_1031,plain,(
    ! [C_139,A_140,B_141] :
      ( v1_relat_1(k2_funct_1(C_139))
      | k2_relset_1(A_140,B_141,C_139) != B_141
      | ~ v2_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_2(C_139,A_140,B_141)
      | ~ v1_funct_1(C_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1020])).

tff(c_1040,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_480,c_1031])).

tff(c_1048,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_481,c_68,c_479,c_1040])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_166,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_163,c_10])).

tff(c_169,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_166])).

tff(c_393,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_169])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_437,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_6])).

tff(c_441,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_437])).

tff(c_146,plain,(
    ! [B_64,A_65] :
      ( k2_relat_1(k7_relat_1(B_64,A_65)) = k9_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_727,plain,(
    ! [B_116,A_117] :
      ( k10_relat_1(k7_relat_1(B_116,A_117),k9_relat_1(B_116,A_117)) = k1_relat_1(k7_relat_1(B_116,A_117))
      | ~ v1_relat_1(k7_relat_1(B_116,A_117))
      | ~ v1_relat_1(B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_8])).

tff(c_751,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = k1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_727])).

tff(c_757,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_129,c_393,c_441,c_393,c_751])).

tff(c_34,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1050,plain,(
    ! [C_142,B_143,A_144] :
      ( v4_relat_1(k2_funct_1(C_142),B_143)
      | k2_relset_1(A_144,B_143,C_142) != B_143
      | ~ v2_funct_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_2(C_142,A_144,B_143)
      | ~ v1_funct_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_996,c_34])).

tff(c_1059,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_480,c_1050])).

tff(c_1067,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_481,c_68,c_479,c_1059])).

tff(c_1074,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1067,c_10])).

tff(c_1080,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1074])).

tff(c_1102,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_6])).

tff(c_1118,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1102])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k9_relat_1(k2_funct_1(B_16),A_15) = k10_relat_1(B_16,A_15)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1141,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_24])).

tff(c_1156,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_76,c_68,c_757,c_1141])).

tff(c_623,plain,(
    ! [B_103,A_104] :
      ( k10_relat_1(k2_funct_1(B_103),A_104) = k9_relat_1(B_103,A_104)
      | ~ v2_funct_1(B_103)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_630,plain,(
    ! [B_103] :
      ( k9_relat_1(B_103,k2_relat_1(k2_funct_1(B_103))) = k1_relat_1(k2_funct_1(B_103))
      | ~ v1_relat_1(k2_funct_1(B_103))
      | ~ v2_funct_1(B_103)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_8])).

tff(c_1166,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_630])).

tff(c_1187,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_76,c_68,c_1048,c_441,c_1166])).

tff(c_489,plain,(
    ! [A_96] :
      ( m1_subset_1(A_96,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96),k2_relat_1(A_96))))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_505,plain,(
    ! [A_96] :
      ( k2_relset_1(k1_relat_1(A_96),k2_relat_1(A_96),A_96) = k2_relat_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_489,c_36])).

tff(c_1232,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_505])).

tff(c_1264,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_725,c_1156,c_1156,c_1232])).

tff(c_1160,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_1118])).

tff(c_504,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(k7_relat_1(B_7,A_6),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(B_7,A_6)),k9_relat_1(B_7,A_6))))
      | ~ v1_funct_1(k7_relat_1(B_7,A_6))
      | ~ v1_relat_1(k7_relat_1(B_7,A_6))
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_489])).

tff(c_1320,plain,
    ( m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_504])).

tff(c_1339,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1048,c_1080,c_725,c_1080,c_1187,c_1080,c_1080,c_1320])).

tff(c_1467,plain,(
    ! [B_155,A_156,C_157] :
      ( k2_relset_1(B_155,A_156,k2_funct_1(C_157)) = k2_relat_1(k2_funct_1(C_157))
      | k2_relset_1(A_156,B_155,C_157) != B_155
      | ~ v2_funct_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155)))
      | ~ v1_funct_2(C_157,A_156,B_155)
      | ~ v1_funct_1(C_157) ) ),
    inference(resolution,[status(thm)],[c_996,c_36])).

tff(c_1470,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1339,c_1467])).

tff(c_1485,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_974,c_1264,c_1470])).

tff(c_1498,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1485])).

tff(c_1501,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1498])).

tff(c_1505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_76,c_68,c_1501])).

tff(c_1507,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1485])).

tff(c_30,plain,(
    ! [A_18,B_20] :
      ( k2_funct_1(A_18) = B_20
      | k6_relat_1(k2_relat_1(A_18)) != k5_relat_1(B_20,A_18)
      | k2_relat_1(B_20) != k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1163,plain,(
    ! [B_20] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_20
      | k5_relat_1(B_20,k2_funct_1('#skF_3')) != k6_relat_1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_20) != k1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_30])).

tff(c_1185,plain,(
    ! [B_20] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_20
      | k5_relat_1(B_20,k2_funct_1('#skF_3')) != k6_relat_1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_20) != k1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_725,c_1163])).

tff(c_1637,plain,(
    ! [B_162] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_162
      | k5_relat_1(B_162,k2_funct_1('#skF_3')) != k6_relat_1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_162) != k2_relat_1('#skF_3')
      | ~ v1_funct_1(B_162)
      | ~ v1_relat_1(B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_1187,c_1185])).

tff(c_1645,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1637])).

tff(c_1651,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_76,c_68,c_1645])).

tff(c_54,plain,(
    ! [A_40] :
      ( m1_subset_1(A_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40))))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_976,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_tops_2(A_133,B_134,C_135) = k2_funct_1(C_135)
      | ~ v2_funct_1(C_135)
      | k2_relset_1(A_133,B_134,C_135) != B_134
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_2(C_135,A_133,B_134)
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_1508,plain,(
    ! [A_158] :
      ( k2_tops_2(k1_relat_1(A_158),k2_relat_1(A_158),A_158) = k2_funct_1(A_158)
      | ~ v2_funct_1(A_158)
      | k2_relset_1(k1_relat_1(A_158),k2_relat_1(A_158),A_158) != k2_relat_1(A_158)
      | ~ v1_funct_2(A_158,k1_relat_1(A_158),k2_relat_1(A_158))
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(resolution,[status(thm)],[c_54,c_976])).

tff(c_1511,plain,
    ( k2_tops_2(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) != k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_1508])).

tff(c_1525,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_725,c_974,c_1156,c_1156,c_1264,c_1156,c_1187,c_1507,c_1156,c_1187,c_1511])).

tff(c_982,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_480,c_976])).

tff(c_989,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_481,c_479,c_68,c_982])).

tff(c_66,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_130,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_92,c_92,c_91,c_91,c_91,c_66])).

tff(c_395,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_390,c_390,c_130])).

tff(c_521,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_474,c_474,c_395])).

tff(c_991,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_521])).

tff(c_1532,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_991])).

tff(c_1662,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_1532])).

tff(c_1675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_1662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:46:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.67  
% 3.92/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.67  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.67  
% 3.92/1.67  %Foreground sorts:
% 3.92/1.67  
% 3.92/1.67  
% 3.92/1.67  %Background operators:
% 3.92/1.67  
% 3.92/1.67  
% 3.92/1.67  %Foreground operators:
% 3.92/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.92/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.92/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.92/1.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.92/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.92/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.92/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.92/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.92/1.67  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.92/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.92/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.92/1.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.92/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.92/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.92/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.92/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.92/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.92/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.92/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.92/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.92/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.92/1.67  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.92/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.92/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.92/1.67  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.92/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.67  
% 4.15/1.70  tff(f_229, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.15/1.70  tff(f_187, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.15/1.70  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.15/1.70  tff(f_195, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.15/1.70  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.15/1.70  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.15/1.70  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.15/1.70  tff(f_143, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.15/1.70  tff(f_135, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.15/1.70  tff(f_157, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.15/1.70  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.15/1.70  tff(f_68, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.15/1.70  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.15/1.70  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.15/1.70  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.15/1.70  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.15/1.70  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 4.15/1.70  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 4.15/1.70  tff(f_183, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.15/1.70  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.15/1.70  tff(f_207, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.15/1.70  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_82, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_84, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.15/1.70  tff(c_92, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_84])).
% 4.15/1.70  tff(c_78, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_91, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_84])).
% 4.15/1.70  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_122, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_91, c_72])).
% 4.15/1.70  tff(c_232, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.70  tff(c_240, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_122, c_232])).
% 4.15/1.70  tff(c_70, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_117, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_91, c_70])).
% 4.15/1.70  tff(c_242, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_117])).
% 4.15/1.70  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_102, plain, (![A_53]: (~v1_xboole_0(u1_struct_0(A_53)) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.15/1.70  tff(c_108, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_102])).
% 4.15/1.70  tff(c_112, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_108])).
% 4.15/1.70  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_112])).
% 4.15/1.70  tff(c_251, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_113])).
% 4.15/1.70  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.15/1.70  tff(c_123, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.70  tff(c_126, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_122, c_123])).
% 4.15/1.70  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126])).
% 4.15/1.70  tff(c_159, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.15/1.70  tff(c_163, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_122, c_159])).
% 4.15/1.70  tff(c_188, plain, (![B_72, A_73]: (k1_relat_1(B_72)=A_73 | ~v1_partfun1(B_72, A_73) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/1.70  tff(c_191, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_163, c_188])).
% 4.15/1.70  tff(c_194, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_191])).
% 4.15/1.70  tff(c_195, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_194])).
% 4.15/1.70  tff(c_74, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_101, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_91, c_74])).
% 4.15/1.70  tff(c_252, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_101])).
% 4.15/1.70  tff(c_250, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_122])).
% 4.15/1.70  tff(c_378, plain, (![C_90, A_91, B_92]: (v1_partfun1(C_90, A_91) | ~v1_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | v1_xboole_0(B_92))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.15/1.70  tff(c_381, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_250, c_378])).
% 4.15/1.70  tff(c_387, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_252, c_381])).
% 4.15/1.70  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_195, c_387])).
% 4.15/1.70  tff(c_390, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_194])).
% 4.15/1.70  tff(c_396, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_122])).
% 4.15/1.70  tff(c_36, plain, (![A_24, B_25, C_26]: (k2_relset_1(A_24, B_25, C_26)=k2_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.70  tff(c_461, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_396, c_36])).
% 4.15/1.70  tff(c_397, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_117])).
% 4.15/1.70  tff(c_474, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_397])).
% 4.15/1.70  tff(c_399, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_101])).
% 4.15/1.70  tff(c_481, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_399])).
% 4.15/1.70  tff(c_480, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_396])).
% 4.15/1.70  tff(c_1199, plain, (![A_145, B_146, C_147, D_148]: (r2_funct_2(A_145, B_146, C_147, C_147) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_2(D_148, A_145, B_146) | ~v1_funct_1(D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_2(C_147, A_145, B_146) | ~v1_funct_1(C_147))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.15/1.70  tff(c_1205, plain, (![C_147]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_147, C_147) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_147, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_147))), inference(resolution, [status(thm)], [c_480, c_1199])).
% 4.15/1.70  tff(c_1278, plain, (![C_149]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_149, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_149, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_149))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_481, c_1205])).
% 4.15/1.70  tff(c_1283, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_480, c_1278])).
% 4.15/1.70  tff(c_1290, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_481, c_1283])).
% 4.15/1.70  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_28, plain, (![A_17]: (k5_relat_1(A_17, k2_funct_1(A_17))=k6_relat_1(k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.15/1.70  tff(c_16, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.15/1.70  tff(c_479, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_461])).
% 4.15/1.70  tff(c_716, plain, (![C_113, A_114, B_115]: (v1_funct_1(k2_funct_1(C_113)) | k2_relset_1(A_114, B_115, C_113)!=B_115 | ~v2_funct_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_2(C_113, A_114, B_115) | ~v1_funct_1(C_113))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.15/1.70  tff(c_719, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_480, c_716])).
% 4.15/1.70  tff(c_725, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_481, c_68, c_479, c_719])).
% 4.15/1.70  tff(c_961, plain, (![C_130, B_131, A_132]: (v1_funct_2(k2_funct_1(C_130), B_131, A_132) | k2_relset_1(A_132, B_131, C_130)!=B_131 | ~v2_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(C_130, A_132, B_131) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.15/1.70  tff(c_967, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_480, c_961])).
% 4.15/1.70  tff(c_974, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_481, c_68, c_479, c_967])).
% 4.15/1.70  tff(c_996, plain, (![C_136, B_137, A_138]: (m1_subset_1(k2_funct_1(C_136), k1_zfmisc_1(k2_zfmisc_1(B_137, A_138))) | k2_relset_1(A_138, B_137, C_136)!=B_137 | ~v2_funct_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_2(C_136, A_138, B_137) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.15/1.70  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.70  tff(c_1020, plain, (![C_136, B_137, A_138]: (v1_relat_1(k2_funct_1(C_136)) | ~v1_relat_1(k2_zfmisc_1(B_137, A_138)) | k2_relset_1(A_138, B_137, C_136)!=B_137 | ~v2_funct_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_2(C_136, A_138, B_137) | ~v1_funct_1(C_136))), inference(resolution, [status(thm)], [c_996, c_2])).
% 4.15/1.70  tff(c_1031, plain, (![C_139, A_140, B_141]: (v1_relat_1(k2_funct_1(C_139)) | k2_relset_1(A_140, B_141, C_139)!=B_141 | ~v2_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_2(C_139, A_140, B_141) | ~v1_funct_1(C_139))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1020])).
% 4.15/1.70  tff(c_1040, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_480, c_1031])).
% 4.15/1.70  tff(c_1048, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_481, c_68, c_479, c_1040])).
% 4.15/1.70  tff(c_10, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/1.70  tff(c_166, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_163, c_10])).
% 4.15/1.70  tff(c_169, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_166])).
% 4.15/1.70  tff(c_393, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_390, c_169])).
% 4.15/1.70  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.70  tff(c_437, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_393, c_6])).
% 4.15/1.70  tff(c_441, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_437])).
% 4.15/1.70  tff(c_146, plain, (![B_64, A_65]: (k2_relat_1(k7_relat_1(B_64, A_65))=k9_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.70  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.15/1.70  tff(c_727, plain, (![B_116, A_117]: (k10_relat_1(k7_relat_1(B_116, A_117), k9_relat_1(B_116, A_117))=k1_relat_1(k7_relat_1(B_116, A_117)) | ~v1_relat_1(k7_relat_1(B_116, A_117)) | ~v1_relat_1(B_116))), inference(superposition, [status(thm), theory('equality')], [c_146, c_8])).
% 4.15/1.70  tff(c_751, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))=k1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_393, c_727])).
% 4.15/1.70  tff(c_757, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_129, c_393, c_441, c_393, c_751])).
% 4.15/1.70  tff(c_34, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.15/1.70  tff(c_1050, plain, (![C_142, B_143, A_144]: (v4_relat_1(k2_funct_1(C_142), B_143) | k2_relset_1(A_144, B_143, C_142)!=B_143 | ~v2_funct_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_2(C_142, A_144, B_143) | ~v1_funct_1(C_142))), inference(resolution, [status(thm)], [c_996, c_34])).
% 4.15/1.70  tff(c_1059, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_480, c_1050])).
% 4.15/1.70  tff(c_1067, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_481, c_68, c_479, c_1059])).
% 4.15/1.70  tff(c_1074, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1067, c_10])).
% 4.15/1.70  tff(c_1080, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_1074])).
% 4.15/1.70  tff(c_1102, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1080, c_6])).
% 4.15/1.70  tff(c_1118, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_1102])).
% 4.15/1.70  tff(c_24, plain, (![B_16, A_15]: (k9_relat_1(k2_funct_1(B_16), A_15)=k10_relat_1(B_16, A_15) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.15/1.70  tff(c_1141, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1118, c_24])).
% 4.15/1.70  tff(c_1156, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_76, c_68, c_757, c_1141])).
% 4.15/1.70  tff(c_623, plain, (![B_103, A_104]: (k10_relat_1(k2_funct_1(B_103), A_104)=k9_relat_1(B_103, A_104) | ~v2_funct_1(B_103) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.70  tff(c_630, plain, (![B_103]: (k9_relat_1(B_103, k2_relat_1(k2_funct_1(B_103)))=k1_relat_1(k2_funct_1(B_103)) | ~v1_relat_1(k2_funct_1(B_103)) | ~v2_funct_1(B_103) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(superposition, [status(thm), theory('equality')], [c_623, c_8])).
% 4.15/1.70  tff(c_1166, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1156, c_630])).
% 4.15/1.70  tff(c_1187, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_76, c_68, c_1048, c_441, c_1166])).
% 4.15/1.70  tff(c_489, plain, (![A_96]: (m1_subset_1(A_96, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96), k2_relat_1(A_96)))) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.15/1.70  tff(c_505, plain, (![A_96]: (k2_relset_1(k1_relat_1(A_96), k2_relat_1(A_96), A_96)=k2_relat_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_489, c_36])).
% 4.15/1.70  tff(c_1232, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1187, c_505])).
% 4.15/1.70  tff(c_1264, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_725, c_1156, c_1156, c_1232])).
% 4.15/1.70  tff(c_1160, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_1118])).
% 4.15/1.70  tff(c_504, plain, (![B_7, A_6]: (m1_subset_1(k7_relat_1(B_7, A_6), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(B_7, A_6)), k9_relat_1(B_7, A_6)))) | ~v1_funct_1(k7_relat_1(B_7, A_6)) | ~v1_relat_1(k7_relat_1(B_7, A_6)) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_6, c_489])).
% 4.15/1.70  tff(c_1320, plain, (m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), k1_relat_1('#skF_3')))) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1160, c_504])).
% 4.15/1.70  tff(c_1339, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_1048, c_1080, c_725, c_1080, c_1187, c_1080, c_1080, c_1320])).
% 4.15/1.70  tff(c_1467, plain, (![B_155, A_156, C_157]: (k2_relset_1(B_155, A_156, k2_funct_1(C_157))=k2_relat_1(k2_funct_1(C_157)) | k2_relset_1(A_156, B_155, C_157)!=B_155 | ~v2_funct_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))) | ~v1_funct_2(C_157, A_156, B_155) | ~v1_funct_1(C_157))), inference(resolution, [status(thm)], [c_996, c_36])).
% 4.15/1.70  tff(c_1470, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1339, c_1467])).
% 4.15/1.70  tff(c_1485, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_974, c_1264, c_1470])).
% 4.15/1.70  tff(c_1498, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1485])).
% 4.15/1.70  tff(c_1501, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1498])).
% 4.15/1.70  tff(c_1505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_76, c_68, c_1501])).
% 4.15/1.70  tff(c_1507, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1485])).
% 4.15/1.70  tff(c_30, plain, (![A_18, B_20]: (k2_funct_1(A_18)=B_20 | k6_relat_1(k2_relat_1(A_18))!=k5_relat_1(B_20, A_18) | k2_relat_1(B_20)!=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.15/1.70  tff(c_1163, plain, (![B_20]: (k2_funct_1(k2_funct_1('#skF_3'))=B_20 | k5_relat_1(B_20, k2_funct_1('#skF_3'))!=k6_relat_1(k1_relat_1('#skF_3')) | k2_relat_1(B_20)!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_30])).
% 4.15/1.70  tff(c_1185, plain, (![B_20]: (k2_funct_1(k2_funct_1('#skF_3'))=B_20 | k5_relat_1(B_20, k2_funct_1('#skF_3'))!=k6_relat_1(k1_relat_1('#skF_3')) | k2_relat_1(B_20)!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_725, c_1163])).
% 4.15/1.70  tff(c_1637, plain, (![B_162]: (k2_funct_1(k2_funct_1('#skF_3'))=B_162 | k5_relat_1(B_162, k2_funct_1('#skF_3'))!=k6_relat_1(k1_relat_1('#skF_3')) | k2_relat_1(B_162)!=k2_relat_1('#skF_3') | ~v1_funct_1(B_162) | ~v1_relat_1(B_162))), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_1187, c_1185])).
% 4.15/1.70  tff(c_1645, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1637])).
% 4.15/1.70  tff(c_1651, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_76, c_68, c_1645])).
% 4.15/1.70  tff(c_54, plain, (![A_40]: (m1_subset_1(A_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)))) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.15/1.70  tff(c_976, plain, (![A_133, B_134, C_135]: (k2_tops_2(A_133, B_134, C_135)=k2_funct_1(C_135) | ~v2_funct_1(C_135) | k2_relset_1(A_133, B_134, C_135)!=B_134 | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_2(C_135, A_133, B_134) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.15/1.70  tff(c_1508, plain, (![A_158]: (k2_tops_2(k1_relat_1(A_158), k2_relat_1(A_158), A_158)=k2_funct_1(A_158) | ~v2_funct_1(A_158) | k2_relset_1(k1_relat_1(A_158), k2_relat_1(A_158), A_158)!=k2_relat_1(A_158) | ~v1_funct_2(A_158, k1_relat_1(A_158), k2_relat_1(A_158)) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(resolution, [status(thm)], [c_54, c_976])).
% 4.15/1.70  tff(c_1511, plain, (k2_tops_2(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))!=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1187, c_1508])).
% 4.15/1.70  tff(c_1525, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_725, c_974, c_1156, c_1156, c_1264, c_1156, c_1187, c_1507, c_1156, c_1187, c_1511])).
% 4.15/1.70  tff(c_982, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_480, c_976])).
% 4.15/1.70  tff(c_989, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_481, c_479, c_68, c_982])).
% 4.15/1.70  tff(c_66, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 4.15/1.70  tff(c_130, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_92, c_92, c_91, c_91, c_91, c_66])).
% 4.15/1.70  tff(c_395, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_390, c_390, c_130])).
% 4.15/1.70  tff(c_521, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_474, c_474, c_395])).
% 4.15/1.70  tff(c_991, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_989, c_521])).
% 4.15/1.70  tff(c_1532, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_991])).
% 4.15/1.70  tff(c_1662, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1651, c_1532])).
% 4.15/1.70  tff(c_1675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1290, c_1662])).
% 4.15/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.70  
% 4.15/1.70  Inference rules
% 4.15/1.70  ----------------------
% 4.15/1.70  #Ref     : 0
% 4.15/1.70  #Sup     : 346
% 4.15/1.70  #Fact    : 0
% 4.15/1.70  #Define  : 0
% 4.15/1.70  #Split   : 3
% 4.15/1.70  #Chain   : 0
% 4.15/1.70  #Close   : 0
% 4.15/1.70  
% 4.15/1.70  Ordering : KBO
% 4.15/1.70  
% 4.15/1.70  Simplification rules
% 4.15/1.70  ----------------------
% 4.15/1.70  #Subsume      : 16
% 4.15/1.70  #Demod        : 661
% 4.15/1.70  #Tautology    : 199
% 4.15/1.70  #SimpNegUnit  : 8
% 4.15/1.70  #BackRed      : 40
% 4.15/1.70  
% 4.15/1.70  #Partial instantiations: 0
% 4.15/1.70  #Strategies tried      : 1
% 4.15/1.70  
% 4.15/1.70  Timing (in seconds)
% 4.15/1.70  ----------------------
% 4.15/1.70  Preprocessing        : 0.37
% 4.15/1.70  Parsing              : 0.20
% 4.15/1.70  CNF conversion       : 0.02
% 4.15/1.70  Main loop            : 0.54
% 4.15/1.70  Inferencing          : 0.19
% 4.15/1.70  Reduction            : 0.20
% 4.15/1.70  Demodulation         : 0.15
% 4.15/1.70  BG Simplification    : 0.03
% 4.15/1.70  Subsumption          : 0.08
% 4.15/1.70  Abstraction          : 0.03
% 4.15/1.70  MUC search           : 0.00
% 4.15/1.71  Cooper               : 0.00
% 4.15/1.71  Total                : 0.97
% 4.15/1.71  Index Insertion      : 0.00
% 4.15/1.71  Index Deletion       : 0.00
% 4.15/1.71  Index Matching       : 0.00
% 4.15/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
