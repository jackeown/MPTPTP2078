%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:39 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  196 (65200 expanded)
%              Number of leaves         :   49 (22687 expanded)
%              Depth                    :   37
%              Number of atoms          :  440 (187136 expanded)
%              Number of equality atoms :  101 (40122 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_192,negated_conjecture,(
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

tff(f_150,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_158,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_146,axiom,(
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
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

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

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_170,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_72,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_80,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_72])).

tff(c_66,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_79,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_72])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_60])).

tff(c_206,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_210,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_206])).

tff(c_58,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_113,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_58])).

tff(c_211,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_113])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_91,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_97,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_91])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_97])).

tff(c_102,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_101])).

tff(c_220,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_102])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_146,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_150,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_106,c_146])).

tff(c_198,plain,(
    ! [B_66,A_67] :
      ( k1_relat_1(B_66) = A_67
      | ~ v1_partfun1(B_66,A_67)
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_201,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_198])).

tff(c_204,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_201])).

tff(c_205,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_89,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_62])).

tff(c_221,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_89])).

tff(c_219,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_106])).

tff(c_282,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_partfun1(C_73,A_74)
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | v1_xboole_0(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_285,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_219,c_282])).

tff(c_288,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_221,c_285])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_205,c_288])).

tff(c_291,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_298,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_106])).

tff(c_30,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_368,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_30])).

tff(c_297,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_113])).

tff(c_376,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_297])).

tff(c_300,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_89])).

tff(c_383,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_300])).

tff(c_382,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_298])).

tff(c_1057,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( r2_funct_2(A_125,B_126,C_127,C_127)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(D_128,A_125,B_126)
      | ~ v1_funct_1(D_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(C_127,A_125,B_126)
      | ~ v1_funct_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1061,plain,(
    ! [C_127] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_127,C_127)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_127,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_382,c_1057])).

tff(c_1080,plain,(
    ! [C_129] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_129,C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_129,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_1061])).

tff(c_1085,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_1080])).

tff(c_1089,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_1085])).

tff(c_381,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_368])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_513,plain,(
    ! [C_90,B_91,A_92] :
      ( v1_funct_2(k2_funct_1(C_90),B_91,A_92)
      | k2_relset_1(A_92,B_91,C_90) != B_91
      | ~ v2_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91)))
      | ~ v1_funct_2(C_90,A_92,B_91)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_516,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_513])).

tff(c_519,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_56,c_381,c_516])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_491,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_funct_1(k2_funct_1(C_86))
      | k2_relset_1(A_87,B_88,C_86) != B_88
      | ~ v2_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_2(C_86,A_87,B_88)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_494,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_491])).

tff(c_497,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_56,c_381,c_494])).

tff(c_16,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_15] :
      ( k2_funct_1(k2_funct_1(A_15)) = A_15
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_391,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(k2_funct_1(B_79),A_80) = k9_relat_1(B_79,A_80)
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_520,plain,(
    ! [A_93,A_94] :
      ( k9_relat_1(k2_funct_1(A_93),A_94) = k10_relat_1(A_93,A_94)
      | ~ v2_funct_1(k2_funct_1(A_93))
      | ~ v1_funct_1(k2_funct_1(A_93))
      | ~ v1_relat_1(k2_funct_1(A_93))
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_391])).

tff(c_526,plain,(
    ! [A_95,A_96] :
      ( k9_relat_1(k2_funct_1(A_95),A_96) = k10_relat_1(A_95,A_96)
      | ~ v1_funct_1(k2_funct_1(A_95))
      | ~ v1_relat_1(k2_funct_1(A_95))
      | ~ v2_funct_1(A_95)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_16,c_520])).

tff(c_532,plain,(
    ! [A_97,A_98] :
      ( k9_relat_1(k2_funct_1(A_97),A_98) = k10_relat_1(A_97,A_98)
      | ~ v1_funct_1(k2_funct_1(A_97))
      | ~ v2_funct_1(A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_14,c_526])).

tff(c_534,plain,(
    ! [A_98] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_98) = k10_relat_1('#skF_3',A_98)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_497,c_532])).

tff(c_543,plain,(
    ! [A_99] : k9_relat_1(k2_funct_1('#skF_3'),A_99) = k10_relat_1('#skF_3',A_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_56,c_534])).

tff(c_128,plain,(
    ! [B_55,A_56] :
      ( k2_relat_1(k7_relat_1(B_55,A_56)) = k9_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [B_55,A_56] :
      ( k10_relat_1(k7_relat_1(B_55,A_56),k9_relat_1(B_55,A_56)) = k1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_553,plain,(
    ! [A_99] :
      ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'),A_99),k10_relat_1('#skF_3',A_99)) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),A_99))
      | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),A_99))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_134])).

tff(c_615,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_553])).

tff(c_618,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_615])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_618])).

tff(c_624,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_553])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_153,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_156,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_153])).

tff(c_295,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_156])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_160,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_6])).

tff(c_164,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_160])).

tff(c_293,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_164])).

tff(c_455,plain,(
    ! [B_84,A_85] :
      ( k10_relat_1(k7_relat_1(B_84,A_85),k9_relat_1(B_84,A_85)) = k1_relat_1(k7_relat_1(B_84,A_85))
      | ~ v1_relat_1(k7_relat_1(B_84,A_85))
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_467,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = k1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_455])).

tff(c_473,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_112,c_295,c_293,c_295,c_467])).

tff(c_541,plain,(
    ! [A_98] : k9_relat_1(k2_funct_1('#skF_3'),A_98) = k10_relat_1('#skF_3',A_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_56,c_534])).

tff(c_657,plain,(
    ! [C_106,B_107,A_108] :
      ( m1_subset_1(k2_funct_1(C_106),k1_zfmisc_1(k2_zfmisc_1(B_107,A_108)))
      | k2_relset_1(A_108,B_107,C_106) != B_107
      | ~ v2_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_106,A_108,B_107)
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_28,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1367,plain,(
    ! [C_144,B_145,A_146] :
      ( v4_relat_1(k2_funct_1(C_144),B_145)
      | k2_relset_1(A_146,B_145,C_144) != B_145
      | ~ v2_funct_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145)))
      | ~ v1_funct_2(C_144,A_146,B_145)
      | ~ v1_funct_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_657,c_28])).

tff(c_1373,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_1367])).

tff(c_1377,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_56,c_381,c_1373])).

tff(c_1383,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1377,c_10])).

tff(c_1389,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_1383])).

tff(c_1402,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_6])).

tff(c_1410,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_473,c_541,c_1402])).

tff(c_1456,plain,(
    ! [B_147,A_148,C_149] :
      ( k2_relset_1(B_147,A_148,k2_funct_1(C_149)) = k2_relat_1(k2_funct_1(C_149))
      | k2_relset_1(A_148,B_147,C_149) != B_147
      | ~ v2_funct_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147)))
      | ~ v1_funct_2(C_149,A_148,B_147)
      | ~ v1_funct_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_657,c_30])).

tff(c_1462,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_1456])).

tff(c_1466,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_56,c_381,c_1462])).

tff(c_1485,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1466])).

tff(c_408,plain,(
    ! [B_79] :
      ( k9_relat_1(B_79,k2_relat_1(k2_funct_1(B_79))) = k1_relat_1(k2_funct_1(B_79))
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k2_funct_1(B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_391])).

tff(c_550,plain,
    ( k10_relat_1('#skF_3',k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_408])).

tff(c_563,plain,
    ( k10_relat_1('#skF_3',k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_550])).

tff(c_644,plain,
    ( k10_relat_1('#skF_3',k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_563])).

tff(c_645,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_644])).

tff(c_648,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_645])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_56,c_112,c_648])).

tff(c_655,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k10_relat_1('#skF_3',k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_700,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_703,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_700])).

tff(c_707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_56,c_703])).

tff(c_709,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_656,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_296,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_150])).

tff(c_708,plain,(
    k10_relat_1('#skF_3',k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_1024,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k10_relat_1('#skF_3',k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_708])).

tff(c_1028,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_56,c_473,c_1024])).

tff(c_36,plain,(
    ! [B_27] :
      ( v1_partfun1(B_27,k1_relat_1(B_27))
      | ~ v4_relat_1(B_27,k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1033,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_36])).

tff(c_1040,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_1028,c_1033])).

tff(c_1066,plain,(
    ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1040])).

tff(c_1069,plain,
    ( ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1066])).

tff(c_1072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_56,c_296,c_1069])).

tff(c_1074,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1040])).

tff(c_1095,plain,
    ( k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1074,c_10])).

tff(c_1104,plain,(
    k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_1095])).

tff(c_1117,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1104])).

tff(c_1125,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64,c_56,c_295,c_1117])).

tff(c_1724,plain,(
    ! [A_161,B_162,A_163] :
      ( m1_subset_1(A_161,k1_zfmisc_1(k2_zfmisc_1(B_162,A_163)))
      | k2_relset_1(A_163,B_162,k2_funct_1(A_161)) != B_162
      | ~ v2_funct_1(k2_funct_1(A_161))
      | ~ m1_subset_1(k2_funct_1(A_161),k1_zfmisc_1(k2_zfmisc_1(A_163,B_162)))
      | ~ v1_funct_2(k2_funct_1(A_161),A_163,B_162)
      | ~ v1_funct_1(k2_funct_1(A_161))
      | ~ v2_funct_1(A_161)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_657])).

tff(c_1727,plain,(
    ! [B_162,A_163] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_162,A_163)))
      | k2_relset_1(A_163,B_162,k2_funct_1(k2_funct_1('#skF_3'))) != B_162
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_163,B_162)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_163,B_162)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_1724])).

tff(c_1737,plain,(
    ! [B_164,A_165] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_164,A_165)))
      | k2_relset_1(A_165,B_164,'#skF_3') != B_164
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_165,B_164)))
      | ~ v1_funct_2('#skF_3',A_165,B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_497,c_709,c_64,c_1125,c_1125,c_56,c_1125,c_1125,c_1727])).

tff(c_52,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_tops_2(A_37,B_38,C_39) = k2_funct_1(C_39)
      | ~ v2_funct_1(C_39)
      | k2_relset_1(A_37,B_38,C_39) != B_38
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1769,plain,(
    ! [B_164,A_165] :
      ( k2_tops_2(B_164,A_165,k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(B_164,A_165,k2_funct_1('#skF_3')) != A_165
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_164,A_165)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(A_165,B_164,'#skF_3') != B_164
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_165,B_164)))
      | ~ v1_funct_2('#skF_3',A_165,B_164) ) ),
    inference(resolution,[status(thm)],[c_1737,c_52])).

tff(c_2171,plain,(
    ! [B_188,A_189] :
      ( k2_tops_2(B_188,A_189,k2_funct_1('#skF_3')) = '#skF_3'
      | k2_relset_1(B_188,A_189,k2_funct_1('#skF_3')) != A_189
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_188,A_189)
      | k2_relset_1(A_189,B_188,'#skF_3') != B_188
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_189,B_188)))
      | ~ v1_funct_2('#skF_3',A_189,B_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_709,c_1125,c_1769])).

tff(c_2174,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_382,c_2171])).

tff(c_2177,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_381,c_519,c_1485,c_2174])).

tff(c_567,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_tops_2(A_100,B_101,C_102) = k2_funct_1(C_102)
      | ~ v2_funct_1(C_102)
      | k2_relset_1(A_100,B_101,C_102) != B_101
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_570,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_567])).

tff(c_573,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_381,c_56,c_570])).

tff(c_54,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_166,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_80,c_79,c_79,c_79,c_54])).

tff(c_294,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_291,c_291,c_166])).

tff(c_425,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_376,c_376,c_294])).

tff(c_574,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_425])).

tff(c_2178,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2177,c_574])).

tff(c_2181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_2178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:01:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.80  
% 4.56/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.81  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.56/1.81  
% 4.56/1.81  %Foreground sorts:
% 4.56/1.81  
% 4.56/1.81  
% 4.56/1.81  %Background operators:
% 4.56/1.81  
% 4.56/1.81  
% 4.56/1.81  %Foreground operators:
% 4.56/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.56/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.56/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.56/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.56/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.56/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.56/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.56/1.81  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.56/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.56/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.56/1.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.56/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.56/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/1.81  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.56/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.56/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.56/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.56/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.56/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.56/1.81  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.56/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.56/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.56/1.81  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.56/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.81  
% 4.83/1.83  tff(f_192, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.83/1.83  tff(f_150, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.83/1.83  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.83/1.83  tff(f_158, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.83/1.83  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.83/1.83  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.83/1.83  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.83/1.83  tff(f_116, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.83/1.83  tff(f_108, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.83/1.83  tff(f_130, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.83/1.83  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.83/1.83  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.83/1.83  tff(f_68, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.83/1.83  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 4.83/1.83  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 4.83/1.83  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.83/1.83  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.83/1.83  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.83/1.83  tff(f_170, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.83/1.83  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_70, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_72, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.83/1.83  tff(c_80, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_72])).
% 4.83/1.83  tff(c_66, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_79, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_72])).
% 4.83/1.83  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_60])).
% 4.83/1.83  tff(c_206, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.83/1.83  tff(c_210, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_206])).
% 4.83/1.83  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_113, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_58])).
% 4.83/1.83  tff(c_211, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_113])).
% 4.83/1.83  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_91, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.83/1.83  tff(c_97, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_91])).
% 4.83/1.83  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_97])).
% 4.83/1.83  tff(c_102, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_101])).
% 4.83/1.83  tff(c_220, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_102])).
% 4.83/1.83  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.83/1.83  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.83/1.83  tff(c_109, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_106, c_2])).
% 4.83/1.83  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_109])).
% 4.83/1.83  tff(c_146, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.83/1.83  tff(c_150, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_106, c_146])).
% 4.83/1.83  tff(c_198, plain, (![B_66, A_67]: (k1_relat_1(B_66)=A_67 | ~v1_partfun1(B_66, A_67) | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.83/1.83  tff(c_201, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_198])).
% 4.83/1.83  tff(c_204, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_201])).
% 4.83/1.83  tff(c_205, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_204])).
% 4.83/1.83  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_89, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_62])).
% 4.83/1.83  tff(c_221, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_89])).
% 4.83/1.83  tff(c_219, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_106])).
% 4.83/1.83  tff(c_282, plain, (![C_73, A_74, B_75]: (v1_partfun1(C_73, A_74) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | v1_xboole_0(B_75))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.83/1.83  tff(c_285, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_219, c_282])).
% 4.83/1.83  tff(c_288, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_221, c_285])).
% 4.83/1.83  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_205, c_288])).
% 4.83/1.83  tff(c_291, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_204])).
% 4.83/1.83  tff(c_298, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_106])).
% 4.83/1.83  tff(c_30, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.83/1.83  tff(c_368, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_30])).
% 4.83/1.83  tff(c_297, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_113])).
% 4.83/1.83  tff(c_376, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_297])).
% 4.83/1.83  tff(c_300, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_89])).
% 4.83/1.83  tff(c_383, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_300])).
% 4.83/1.83  tff(c_382, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_298])).
% 4.83/1.83  tff(c_1057, plain, (![A_125, B_126, C_127, D_128]: (r2_funct_2(A_125, B_126, C_127, C_127) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(D_128, A_125, B_126) | ~v1_funct_1(D_128) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(C_127, A_125, B_126) | ~v1_funct_1(C_127))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.83/1.83  tff(c_1061, plain, (![C_127]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_127, C_127) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_127, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_127))), inference(resolution, [status(thm)], [c_382, c_1057])).
% 4.83/1.83  tff(c_1080, plain, (![C_129]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_129, C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_129, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_129))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_1061])).
% 4.83/1.83  tff(c_1085, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_382, c_1080])).
% 4.83/1.83  tff(c_1089, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_1085])).
% 4.83/1.83  tff(c_381, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_368])).
% 4.83/1.83  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_513, plain, (![C_90, B_91, A_92]: (v1_funct_2(k2_funct_1(C_90), B_91, A_92) | k2_relset_1(A_92, B_91, C_90)!=B_91 | ~v2_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))) | ~v1_funct_2(C_90, A_92, B_91) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.83  tff(c_516, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_382, c_513])).
% 4.83/1.83  tff(c_519, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_56, c_381, c_516])).
% 4.83/1.83  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.83/1.83  tff(c_491, plain, (![C_86, A_87, B_88]: (v1_funct_1(k2_funct_1(C_86)) | k2_relset_1(A_87, B_88, C_86)!=B_88 | ~v2_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_2(C_86, A_87, B_88) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.83  tff(c_494, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_382, c_491])).
% 4.83/1.83  tff(c_497, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_56, c_381, c_494])).
% 4.83/1.83  tff(c_16, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.83  tff(c_24, plain, (![A_15]: (k2_funct_1(k2_funct_1(A_15))=A_15 | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.83  tff(c_391, plain, (![B_79, A_80]: (k10_relat_1(k2_funct_1(B_79), A_80)=k9_relat_1(B_79, A_80) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.83/1.83  tff(c_520, plain, (![A_93, A_94]: (k9_relat_1(k2_funct_1(A_93), A_94)=k10_relat_1(A_93, A_94) | ~v2_funct_1(k2_funct_1(A_93)) | ~v1_funct_1(k2_funct_1(A_93)) | ~v1_relat_1(k2_funct_1(A_93)) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_24, c_391])).
% 4.83/1.83  tff(c_526, plain, (![A_95, A_96]: (k9_relat_1(k2_funct_1(A_95), A_96)=k10_relat_1(A_95, A_96) | ~v1_funct_1(k2_funct_1(A_95)) | ~v1_relat_1(k2_funct_1(A_95)) | ~v2_funct_1(A_95) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_16, c_520])).
% 4.83/1.83  tff(c_532, plain, (![A_97, A_98]: (k9_relat_1(k2_funct_1(A_97), A_98)=k10_relat_1(A_97, A_98) | ~v1_funct_1(k2_funct_1(A_97)) | ~v2_funct_1(A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_14, c_526])).
% 4.83/1.83  tff(c_534, plain, (![A_98]: (k9_relat_1(k2_funct_1('#skF_3'), A_98)=k10_relat_1('#skF_3', A_98) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_497, c_532])).
% 4.83/1.83  tff(c_543, plain, (![A_99]: (k9_relat_1(k2_funct_1('#skF_3'), A_99)=k10_relat_1('#skF_3', A_99))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_56, c_534])).
% 4.83/1.83  tff(c_128, plain, (![B_55, A_56]: (k2_relat_1(k7_relat_1(B_55, A_56))=k9_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.83/1.83  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.83/1.83  tff(c_134, plain, (![B_55, A_56]: (k10_relat_1(k7_relat_1(B_55, A_56), k9_relat_1(B_55, A_56))=k1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 4.83/1.83  tff(c_553, plain, (![A_99]: (k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'), A_99), k10_relat_1('#skF_3', A_99))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), A_99)) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), A_99)) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_543, c_134])).
% 4.83/1.83  tff(c_615, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_553])).
% 4.83/1.83  tff(c_618, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_615])).
% 4.83/1.83  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_618])).
% 4.83/1.83  tff(c_624, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_553])).
% 4.83/1.83  tff(c_10, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.83/1.83  tff(c_153, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_10])).
% 4.83/1.83  tff(c_156, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_153])).
% 4.83/1.83  tff(c_295, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_291, c_156])).
% 4.83/1.83  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.83/1.83  tff(c_160, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_156, c_6])).
% 4.83/1.83  tff(c_164, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_160])).
% 4.83/1.83  tff(c_293, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_164])).
% 4.83/1.83  tff(c_455, plain, (![B_84, A_85]: (k10_relat_1(k7_relat_1(B_84, A_85), k9_relat_1(B_84, A_85))=k1_relat_1(k7_relat_1(B_84, A_85)) | ~v1_relat_1(k7_relat_1(B_84, A_85)) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 4.83/1.83  tff(c_467, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))=k1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_295, c_455])).
% 4.83/1.83  tff(c_473, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_112, c_295, c_293, c_295, c_467])).
% 4.83/1.83  tff(c_541, plain, (![A_98]: (k9_relat_1(k2_funct_1('#skF_3'), A_98)=k10_relat_1('#skF_3', A_98))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_56, c_534])).
% 4.83/1.83  tff(c_657, plain, (![C_106, B_107, A_108]: (m1_subset_1(k2_funct_1(C_106), k1_zfmisc_1(k2_zfmisc_1(B_107, A_108))) | k2_relset_1(A_108, B_107, C_106)!=B_107 | ~v2_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_106, A_108, B_107) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.83  tff(c_28, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.83/1.83  tff(c_1367, plain, (![C_144, B_145, A_146]: (v4_relat_1(k2_funct_1(C_144), B_145) | k2_relset_1(A_146, B_145, C_144)!=B_145 | ~v2_funct_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))) | ~v1_funct_2(C_144, A_146, B_145) | ~v1_funct_1(C_144))), inference(resolution, [status(thm)], [c_657, c_28])).
% 4.83/1.83  tff(c_1373, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_382, c_1367])).
% 4.83/1.83  tff(c_1377, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_56, c_381, c_1373])).
% 4.83/1.83  tff(c_1383, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1377, c_10])).
% 4.83/1.83  tff(c_1389, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_624, c_1383])).
% 4.83/1.83  tff(c_1402, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1389, c_6])).
% 4.83/1.83  tff(c_1410, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_624, c_473, c_541, c_1402])).
% 4.83/1.83  tff(c_1456, plain, (![B_147, A_148, C_149]: (k2_relset_1(B_147, A_148, k2_funct_1(C_149))=k2_relat_1(k2_funct_1(C_149)) | k2_relset_1(A_148, B_147, C_149)!=B_147 | ~v2_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))) | ~v1_funct_2(C_149, A_148, B_147) | ~v1_funct_1(C_149))), inference(resolution, [status(thm)], [c_657, c_30])).
% 4.83/1.83  tff(c_1462, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_382, c_1456])).
% 4.83/1.83  tff(c_1466, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_56, c_381, c_1462])).
% 4.83/1.83  tff(c_1485, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1466])).
% 4.83/1.83  tff(c_408, plain, (![B_79]: (k9_relat_1(B_79, k2_relat_1(k2_funct_1(B_79)))=k1_relat_1(k2_funct_1(B_79)) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(k2_funct_1(B_79)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_391])).
% 4.83/1.83  tff(c_550, plain, (k10_relat_1('#skF_3', k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_543, c_408])).
% 4.83/1.83  tff(c_563, plain, (k10_relat_1('#skF_3', k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_497, c_550])).
% 4.83/1.83  tff(c_644, plain, (k10_relat_1('#skF_3', k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_563])).
% 4.83/1.83  tff(c_645, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_644])).
% 4.83/1.83  tff(c_648, plain, (~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_645])).
% 4.83/1.83  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_56, c_112, c_648])).
% 4.83/1.83  tff(c_655, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k10_relat_1('#skF_3', k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_644])).
% 4.83/1.83  tff(c_700, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_655])).
% 4.83/1.83  tff(c_703, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_700])).
% 4.83/1.83  tff(c_707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_56, c_703])).
% 4.83/1.83  tff(c_709, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_655])).
% 4.83/1.83  tff(c_656, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_644])).
% 4.83/1.83  tff(c_296, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_150])).
% 4.83/1.83  tff(c_708, plain, (k10_relat_1('#skF_3', k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_655])).
% 4.83/1.83  tff(c_1024, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k10_relat_1('#skF_3', k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_708])).
% 4.83/1.83  tff(c_1028, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_56, c_473, c_1024])).
% 4.83/1.83  tff(c_36, plain, (![B_27]: (v1_partfun1(B_27, k1_relat_1(B_27)) | ~v4_relat_1(B_27, k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.83/1.83  tff(c_1033, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1028, c_36])).
% 4.83/1.83  tff(c_1040, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_1028, c_1033])).
% 4.83/1.83  tff(c_1066, plain, (~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1040])).
% 4.83/1.83  tff(c_1069, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1066])).
% 4.83/1.83  tff(c_1072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_56, c_296, c_1069])).
% 4.83/1.83  tff(c_1074, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1040])).
% 4.83/1.83  tff(c_1095, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1074, c_10])).
% 4.83/1.83  tff(c_1104, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_1095])).
% 4.83/1.83  tff(c_1117, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1104])).
% 4.83/1.83  tff(c_1125, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_64, c_56, c_295, c_1117])).
% 4.83/1.83  tff(c_1724, plain, (![A_161, B_162, A_163]: (m1_subset_1(A_161, k1_zfmisc_1(k2_zfmisc_1(B_162, A_163))) | k2_relset_1(A_163, B_162, k2_funct_1(A_161))!=B_162 | ~v2_funct_1(k2_funct_1(A_161)) | ~m1_subset_1(k2_funct_1(A_161), k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))) | ~v1_funct_2(k2_funct_1(A_161), A_163, B_162) | ~v1_funct_1(k2_funct_1(A_161)) | ~v2_funct_1(A_161) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(superposition, [status(thm), theory('equality')], [c_24, c_657])).
% 4.83/1.83  tff(c_1727, plain, (![B_162, A_163]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_162, A_163))) | k2_relset_1(A_163, B_162, k2_funct_1(k2_funct_1('#skF_3')))!=B_162 | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_163, B_162) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1125, c_1724])).
% 4.83/1.83  tff(c_1737, plain, (![B_164, A_165]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_164, A_165))) | k2_relset_1(A_165, B_164, '#skF_3')!=B_164 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))) | ~v1_funct_2('#skF_3', A_165, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_497, c_709, c_64, c_1125, c_1125, c_56, c_1125, c_1125, c_1727])).
% 4.83/1.83  tff(c_52, plain, (![A_37, B_38, C_39]: (k2_tops_2(A_37, B_38, C_39)=k2_funct_1(C_39) | ~v2_funct_1(C_39) | k2_relset_1(A_37, B_38, C_39)!=B_38 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(C_39, A_37, B_38) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.83/1.83  tff(c_1769, plain, (![B_164, A_165]: (k2_tops_2(B_164, A_165, k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(B_164, A_165, k2_funct_1('#skF_3'))!=A_165 | ~v1_funct_2(k2_funct_1('#skF_3'), B_164, A_165) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(A_165, B_164, '#skF_3')!=B_164 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))) | ~v1_funct_2('#skF_3', A_165, B_164))), inference(resolution, [status(thm)], [c_1737, c_52])).
% 4.83/1.83  tff(c_2171, plain, (![B_188, A_189]: (k2_tops_2(B_188, A_189, k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(B_188, A_189, k2_funct_1('#skF_3'))!=A_189 | ~v1_funct_2(k2_funct_1('#skF_3'), B_188, A_189) | k2_relset_1(A_189, B_188, '#skF_3')!=B_188 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))) | ~v1_funct_2('#skF_3', A_189, B_188))), inference(demodulation, [status(thm), theory('equality')], [c_497, c_709, c_1125, c_1769])).
% 4.83/1.83  tff(c_2174, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_382, c_2171])).
% 4.83/1.83  tff(c_2177, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_381, c_519, c_1485, c_2174])).
% 4.83/1.83  tff(c_567, plain, (![A_100, B_101, C_102]: (k2_tops_2(A_100, B_101, C_102)=k2_funct_1(C_102) | ~v2_funct_1(C_102) | k2_relset_1(A_100, B_101, C_102)!=B_101 | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(C_102, A_100, B_101) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.83/1.83  tff(c_570, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_382, c_567])).
% 4.83/1.83  tff(c_573, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_381, c_56, c_570])).
% 4.83/1.83  tff(c_54, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.83/1.83  tff(c_166, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_80, c_79, c_79, c_79, c_54])).
% 4.83/1.83  tff(c_294, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_291, c_291, c_166])).
% 4.83/1.83  tff(c_425, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_376, c_376, c_294])).
% 4.83/1.83  tff(c_574, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_425])).
% 4.83/1.83  tff(c_2178, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2177, c_574])).
% 4.83/1.83  tff(c_2181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1089, c_2178])).
% 4.83/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.83  
% 4.83/1.83  Inference rules
% 4.83/1.83  ----------------------
% 4.83/1.83  #Ref     : 0
% 4.83/1.84  #Sup     : 454
% 4.83/1.84  #Fact    : 0
% 4.83/1.84  #Define  : 0
% 4.83/1.84  #Split   : 12
% 4.83/1.84  #Chain   : 0
% 4.83/1.84  #Close   : 0
% 4.83/1.84  
% 4.83/1.84  Ordering : KBO
% 4.83/1.84  
% 4.83/1.84  Simplification rules
% 4.83/1.84  ----------------------
% 4.83/1.84  #Subsume      : 26
% 4.83/1.84  #Demod        : 1195
% 4.83/1.84  #Tautology    : 290
% 4.83/1.84  #SimpNegUnit  : 9
% 4.83/1.84  #BackRed      : 51
% 4.83/1.84  
% 4.83/1.84  #Partial instantiations: 0
% 4.83/1.84  #Strategies tried      : 1
% 4.83/1.84  
% 4.83/1.84  Timing (in seconds)
% 4.83/1.84  ----------------------
% 4.83/1.84  Preprocessing        : 0.35
% 4.83/1.84  Parsing              : 0.19
% 4.83/1.84  CNF conversion       : 0.02
% 4.83/1.84  Main loop            : 0.68
% 4.83/1.84  Inferencing          : 0.23
% 4.83/1.84  Reduction            : 0.26
% 4.83/1.84  Demodulation         : 0.18
% 4.83/1.84  BG Simplification    : 0.03
% 4.83/1.84  Subsumption          : 0.11
% 4.83/1.84  Abstraction          : 0.03
% 4.83/1.84  MUC search           : 0.00
% 4.83/1.84  Cooper               : 0.00
% 4.83/1.84  Total                : 1.09
% 4.83/1.84  Index Insertion      : 0.00
% 4.83/1.84  Index Deletion       : 0.00
% 4.83/1.84  Index Matching       : 0.00
% 4.83/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
