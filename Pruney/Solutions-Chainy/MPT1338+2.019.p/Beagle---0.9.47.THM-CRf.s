%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:16 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :  259 (194438 expanded)
%              Number of leaves         :   54 (67642 expanded)
%              Depth                    :   41
%              Number of atoms          :  613 (603695 expanded)
%              Number of equality atoms :  161 (193011 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_159,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_155,axiom,(
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

tff(f_179,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_82,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_101,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_109,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_101])).

tff(c_78,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_108,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_101])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_136,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_72])).

tff(c_2451,plain,(
    ! [A_201,B_202,C_203] :
      ( k2_relset_1(A_201,B_202,C_203) = k2_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2455,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_2451])).

tff(c_70,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_154,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_70])).

tff(c_2456,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_154])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_120,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_126,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_120])).

tff(c_130,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_126])).

tff(c_131,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_130])).

tff(c_2465,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_131])).

tff(c_32,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_140,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_32])).

tff(c_179,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_183,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_136,c_179])).

tff(c_2442,plain,(
    ! [B_198,A_199] :
      ( k1_relat_1(B_198) = A_199
      | ~ v1_partfun1(B_198,A_199)
      | ~ v4_relat_1(B_198,A_199)
      | ~ v1_relat_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2445,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_2442])).

tff(c_2448,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2445])).

tff(c_2449,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2448])).

tff(c_74,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_114,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_74])).

tff(c_115,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_114])).

tff(c_2466,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_115])).

tff(c_2464,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_136])).

tff(c_2627,plain,(
    ! [C_221,A_222,B_223] :
      ( v1_partfun1(C_221,A_222)
      | ~ v1_funct_2(C_221,A_222,B_223)
      | ~ v1_funct_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | v1_xboole_0(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2630,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2464,c_2627])).

tff(c_2633,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2466,c_2630])).

tff(c_2635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2465,c_2449,c_2633])).

tff(c_2636,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2448])).

tff(c_2642,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_136])).

tff(c_38,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2690,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2642,c_38])).

tff(c_2641,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_154])).

tff(c_2697,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_2641])).

tff(c_2644,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_115])).

tff(c_2704,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2697,c_2644])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2702,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2697,c_2690])).

tff(c_2703,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2697,c_2642])).

tff(c_3061,plain,(
    ! [C_268,B_269,A_270] :
      ( m1_subset_1(k2_funct_1(C_268),k1_zfmisc_1(k2_zfmisc_1(B_269,A_270)))
      | k2_relset_1(A_270,B_269,C_268) != B_269
      | ~ v2_funct_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,B_269)))
      | ~ v1_funct_2(C_268,A_270,B_269)
      | ~ v1_funct_1(C_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3683,plain,(
    ! [B_287,A_288,C_289] :
      ( k2_relset_1(B_287,A_288,k2_funct_1(C_289)) = k2_relat_1(k2_funct_1(C_289))
      | k2_relset_1(A_288,B_287,C_289) != B_287
      | ~ v2_funct_1(C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287)))
      | ~ v1_funct_2(C_289,A_288,B_287)
      | ~ v1_funct_1(C_289) ) ),
    inference(resolution,[status(thm)],[c_3061,c_38])).

tff(c_3689,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2703,c_3683])).

tff(c_3693,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2704,c_68,c_2702,c_3689])).

tff(c_2965,plain,(
    ! [A_262,B_263,C_264] :
      ( k2_tops_2(A_262,B_263,C_264) = k2_funct_1(C_264)
      | ~ v2_funct_1(C_264)
      | k2_relset_1(A_262,B_263,C_264) != B_263
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ v1_funct_2(C_264,A_262,B_263)
      | ~ v1_funct_1(C_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2968,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2703,c_2965])).

tff(c_2971,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2704,c_2702,c_68,c_2968])).

tff(c_225,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_229,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_225])).

tff(c_230,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_154])).

tff(c_238,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_131])).

tff(c_218,plain,(
    ! [B_67,A_68] :
      ( k1_relat_1(B_67) = A_68
      | ~ v1_partfun1(B_67,A_68)
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_221,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_218])).

tff(c_224,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_221])).

tff(c_278,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_239,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_115])).

tff(c_237,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_136])).

tff(c_398,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_partfun1(C_90,A_91)
      | ~ v1_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | v1_xboole_0(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_401,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_237,c_398])).

tff(c_404,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_239,c_401])).

tff(c_406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_278,c_404])).

tff(c_407,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_411,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_239])).

tff(c_267,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_237,c_38])).

tff(c_454,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_267])).

tff(c_410,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_237])).

tff(c_780,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_tops_2(A_134,B_135,C_136) = k2_funct_1(C_136)
      | ~ v2_funct_1(C_136)
      | k2_relset_1(A_134,B_135,C_136) != B_135
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(C_136,A_134,B_135)
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_783,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_410,c_780])).

tff(c_786,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_411,c_454,c_68,c_783])).

tff(c_66,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_184,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_109,c_108,c_108,c_109,c_109,c_108,c_108,c_66])).

tff(c_185,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_459,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_407,c_230,c_230,c_230,c_185])).

tff(c_787,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_459])).

tff(c_30,plain,(
    ! [A_10] :
      ( k2_funct_1(k2_funct_1(A_10)) = A_10
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_4] :
      ( v1_relat_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_606,plain,(
    ! [C_115,A_116,B_117] :
      ( v1_funct_1(k2_funct_1(C_115))
      | k2_relset_1(A_116,B_117,C_115) != B_117
      | ~ v2_funct_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(C_115,A_116,B_117)
      | ~ v1_funct_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_609,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_410,c_606])).

tff(c_612,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_411,c_68,c_454,c_609])).

tff(c_14,plain,(
    ! [A_5] :
      ( v2_funct_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_535,plain,(
    ! [B_98,A_99] :
      ( k9_relat_1(k2_funct_1(B_98),A_99) = k10_relat_1(B_98,A_99)
      | ~ v2_funct_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_613,plain,(
    ! [A_118,A_119] :
      ( k10_relat_1(k2_funct_1(A_118),A_119) = k9_relat_1(A_118,A_119)
      | ~ v2_funct_1(k2_funct_1(A_118))
      | ~ v1_funct_1(k2_funct_1(A_118))
      | ~ v1_relat_1(k2_funct_1(A_118))
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_535])).

tff(c_626,plain,(
    ! [A_123,A_124] :
      ( k10_relat_1(k2_funct_1(A_123),A_124) = k9_relat_1(A_123,A_124)
      | ~ v1_funct_1(k2_funct_1(A_123))
      | ~ v1_relat_1(k2_funct_1(A_123))
      | ~ v2_funct_1(A_123)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_14,c_613])).

tff(c_632,plain,(
    ! [A_125,A_126] :
      ( k10_relat_1(k2_funct_1(A_125),A_126) = k9_relat_1(A_125,A_126)
      | ~ v1_funct_1(k2_funct_1(A_125))
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(resolution,[status(thm)],[c_12,c_626])).

tff(c_634,plain,(
    ! [A_126] :
      ( k10_relat_1(k2_funct_1('#skF_3'),A_126) = k9_relat_1('#skF_3',A_126)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_612,c_632])).

tff(c_643,plain,(
    ! [A_127] : k10_relat_1(k2_funct_1('#skF_3'),A_127) = k9_relat_1('#skF_3',A_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_634])).

tff(c_4,plain,(
    ! [A_2] :
      ( k10_relat_1(A_2,k2_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_654,plain,
    ( k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_4])).

tff(c_672,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_682,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_672])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_682])).

tff(c_688,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_542,plain,(
    ! [B_98] :
      ( k10_relat_1(B_98,k1_relat_1(k2_funct_1(B_98))) = k2_relat_1(k2_funct_1(B_98))
      | ~ v1_relat_1(k2_funct_1(B_98))
      | ~ v2_funct_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_2])).

tff(c_650,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_542])).

tff(c_668,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_650])).

tff(c_769,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_668])).

tff(c_770,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_769])).

tff(c_773,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_770])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_773])).

tff(c_779,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_769])).

tff(c_661,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_643])).

tff(c_671,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_661])).

tff(c_793,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_779,c_671])).

tff(c_794,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_793])).

tff(c_797,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_794])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_140,c_797])).

tff(c_804,plain,(
    k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_793])).

tff(c_815,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_804])).

tff(c_819,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_815])).

tff(c_831,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_819])).

tff(c_839,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_831])).

tff(c_641,plain,(
    ! [A_126] : k10_relat_1(k2_funct_1('#skF_3'),A_126) = k9_relat_1('#skF_3',A_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_634])).

tff(c_857,plain,(
    ! [C_137,B_138,A_139] :
      ( m1_subset_1(k2_funct_1(C_137),k1_zfmisc_1(k2_zfmisc_1(B_138,A_139)))
      | k2_relset_1(A_139,B_138,C_137) != B_138
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_2(C_137,A_139,B_138)
      | ~ v1_funct_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_40,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k8_relset_1(A_20,B_21,C_22,D_23) = k10_relat_1(C_22,D_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2097,plain,(
    ! [B_179,A_180,C_181,D_182] :
      ( k8_relset_1(B_179,A_180,k2_funct_1(C_181),D_182) = k10_relat_1(k2_funct_1(C_181),D_182)
      | k2_relset_1(A_180,B_179,C_181) != B_179
      | ~ v2_funct_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_180,B_179)))
      | ~ v1_funct_2(C_181,A_180,B_179)
      | ~ v1_funct_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_857,c_40])).

tff(c_2101,plain,(
    ! [D_182] :
      ( k8_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'),D_182) = k10_relat_1(k2_funct_1('#skF_3'),D_182)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_410,c_2097])).

tff(c_2105,plain,(
    ! [D_182] : k8_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'),D_182) = k9_relat_1('#skF_3',D_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_411,c_68,c_454,c_641,c_2101])).

tff(c_42,plain,(
    ! [A_24,B_25,C_26] :
      ( k8_relset_1(A_24,B_25,C_26,B_25) = k1_relset_1(A_24,B_25,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2393,plain,(
    ! [B_192,A_193,C_194] :
      ( k8_relset_1(B_192,A_193,k2_funct_1(C_194),A_193) = k1_relset_1(B_192,A_193,k2_funct_1(C_194))
      | k2_relset_1(A_193,B_192,C_194) != B_192
      | ~ v2_funct_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192)))
      | ~ v1_funct_2(C_194,A_193,B_192)
      | ~ v1_funct_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_857,c_42])).

tff(c_2397,plain,
    ( k8_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_410,c_2393])).

tff(c_2401,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_411,c_68,c_454,c_839,c_2105,c_2397])).

tff(c_2403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_2401])).

tff(c_2404,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2638,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_2636,c_2636,c_2404])).

tff(c_2850,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2697,c_2697,c_2638])).

tff(c_2972,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_2850])).

tff(c_3694,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3693,c_2972])).

tff(c_2889,plain,(
    ! [C_249,A_250,B_251] :
      ( v1_funct_1(k2_funct_1(C_249))
      | k2_relset_1(A_250,B_251,C_249) != B_251
      | ~ v2_funct_1(C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_2(C_249,A_250,B_251)
      | ~ v1_funct_1(C_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2892,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2703,c_2889])).

tff(c_2895,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2704,c_68,c_2702,c_2892])).

tff(c_2722,plain,(
    ! [B_227,A_228] :
      ( k9_relat_1(k2_funct_1(B_227),A_228) = k10_relat_1(B_227,A_228)
      | ~ v2_funct_1(B_227)
      | ~ v1_funct_1(B_227)
      | ~ v1_relat_1(B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2896,plain,(
    ! [A_252,A_253] :
      ( k10_relat_1(k2_funct_1(A_252),A_253) = k9_relat_1(A_252,A_253)
      | ~ v2_funct_1(k2_funct_1(A_252))
      | ~ v1_funct_1(k2_funct_1(A_252))
      | ~ v1_relat_1(k2_funct_1(A_252))
      | ~ v2_funct_1(A_252)
      | ~ v1_funct_1(A_252)
      | ~ v1_relat_1(A_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2722])).

tff(c_2902,plain,(
    ! [A_254,A_255] :
      ( k10_relat_1(k2_funct_1(A_254),A_255) = k9_relat_1(A_254,A_255)
      | ~ v1_funct_1(k2_funct_1(A_254))
      | ~ v1_relat_1(k2_funct_1(A_254))
      | ~ v2_funct_1(A_254)
      | ~ v1_funct_1(A_254)
      | ~ v1_relat_1(A_254) ) ),
    inference(resolution,[status(thm)],[c_14,c_2896])).

tff(c_2915,plain,(
    ! [A_259,A_260] :
      ( k10_relat_1(k2_funct_1(A_259),A_260) = k9_relat_1(A_259,A_260)
      | ~ v1_funct_1(k2_funct_1(A_259))
      | ~ v2_funct_1(A_259)
      | ~ v1_funct_1(A_259)
      | ~ v1_relat_1(A_259) ) ),
    inference(resolution,[status(thm)],[c_12,c_2902])).

tff(c_2917,plain,(
    ! [A_260] :
      ( k10_relat_1(k2_funct_1('#skF_3'),A_260) = k9_relat_1('#skF_3',A_260)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2895,c_2915])).

tff(c_2926,plain,(
    ! [A_261] : k10_relat_1(k2_funct_1('#skF_3'),A_261) = k9_relat_1('#skF_3',A_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_2917])).

tff(c_2937,plain,
    ( k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2926,c_4])).

tff(c_2955,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2937])).

tff(c_2958,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_2955])).

tff(c_2962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_2958])).

tff(c_2964,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2937])).

tff(c_2739,plain,(
    ! [B_227] :
      ( k10_relat_1(B_227,k1_relat_1(k2_funct_1(B_227))) = k2_relat_1(k2_funct_1(B_227))
      | ~ v2_funct_1(B_227)
      | ~ v1_funct_1(B_227)
      | ~ v1_relat_1(B_227)
      | ~ v1_relat_1(k2_funct_1(B_227)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2722])).

tff(c_2944,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2739,c_2926])).

tff(c_2954,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2895,c_2944])).

tff(c_3107,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2964,c_2954])).

tff(c_3108,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3107])).

tff(c_3111,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3108])).

tff(c_3117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_140,c_3111])).

tff(c_3119,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3107])).

tff(c_2933,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2926,c_2739])).

tff(c_2951,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2895,c_2933])).

tff(c_3126,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_2964,c_2951])).

tff(c_3127,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3126])).

tff(c_3130,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3127])).

tff(c_3134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_3130])).

tff(c_3136,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3126])).

tff(c_3135,plain,(
    k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3126])).

tff(c_3141,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3135])).

tff(c_3145,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_3141])).

tff(c_3157,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3145])).

tff(c_3165,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_3157])).

tff(c_3166,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_3145])).

tff(c_10,plain,(
    ! [A_4] :
      ( v1_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2988,plain,(
    ! [A_265,A_266] :
      ( k10_relat_1(k2_funct_1(A_265),A_266) = k9_relat_1(A_265,A_266)
      | ~ v2_funct_1(A_265)
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(resolution,[status(thm)],[c_10,c_2915])).

tff(c_3003,plain,(
    ! [A_265] :
      ( k9_relat_1(A_265,k2_relat_1(k2_funct_1(A_265))) = k1_relat_1(k2_funct_1(A_265))
      | ~ v1_relat_1(k2_funct_1(A_265))
      | ~ v2_funct_1(A_265)
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2988,c_4])).

tff(c_3197,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3166,c_3003])).

tff(c_3207,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2964,c_2895,c_3136,c_3119,c_3197])).

tff(c_20,plain,(
    ! [B_7,A_6] :
      ( k9_relat_1(k2_funct_1(B_7),A_6) = k10_relat_1(B_7,A_6)
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3217,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k10_relat_1('#skF_3',k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3207,c_20])).

tff(c_3224,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k10_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_3217])).

tff(c_3242,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3224])).

tff(c_3252,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_3242])).

tff(c_3265,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3252,c_3224])).

tff(c_2806,plain,(
    ! [A_232] :
      ( k2_relat_1(k5_relat_1(A_232,k2_funct_1(A_232))) = k1_relat_1(A_232)
      | ~ v2_funct_1(A_232)
      | ~ v1_funct_1(A_232)
      | ~ v1_relat_1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3315,plain,(
    ! [A_274] :
      ( k10_relat_1(k5_relat_1(A_274,k2_funct_1(A_274)),k1_relat_1(A_274)) = k1_relat_1(k5_relat_1(A_274,k2_funct_1(A_274)))
      | ~ v1_relat_1(k5_relat_1(A_274,k2_funct_1(A_274)))
      | ~ v2_funct_1(A_274)
      | ~ v1_funct_1(A_274)
      | ~ v1_relat_1(A_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2806,c_4])).

tff(c_3324,plain,
    ( k10_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))),k1_relat_1('#skF_3')) = k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3265,c_3315])).

tff(c_3340,plain,
    ( k10_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))),k1_relat_1('#skF_3')) = k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_3324])).

tff(c_3476,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3340])).

tff(c_3479,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3476])).

tff(c_3485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_76,c_3479])).

tff(c_3487,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3340])).

tff(c_2784,plain,(
    ! [A_231] :
      ( k1_relat_1(k5_relat_1(A_231,k2_funct_1(A_231))) = k1_relat_1(A_231)
      | ~ v2_funct_1(A_231)
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3613,plain,(
    ! [A_285] :
      ( k9_relat_1(k5_relat_1(A_285,k2_funct_1(A_285)),k1_relat_1(A_285)) = k2_relat_1(k5_relat_1(A_285,k2_funct_1(A_285)))
      | ~ v1_relat_1(k5_relat_1(A_285,k2_funct_1(A_285)))
      | ~ v2_funct_1(A_285)
      | ~ v1_funct_1(A_285)
      | ~ v1_relat_1(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2784,c_2])).

tff(c_3628,plain,
    ( k9_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))),k1_relat_1('#skF_3')) = k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3265,c_3613])).

tff(c_3644,plain,
    ( k9_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))),k1_relat_1('#skF_3')) = k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_3487,c_3628])).

tff(c_3728,plain,(
    ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3644])).

tff(c_3731,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3728])).

tff(c_3737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76,c_68,c_68,c_3731])).

tff(c_3739,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3644])).

tff(c_6,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_relat_1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3532,plain,(
    ! [A_277] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_277),A_277)) = k1_relat_1(k2_funct_1(A_277))
      | ~ v2_funct_1(k2_funct_1(A_277))
      | ~ v1_funct_1(k2_funct_1(A_277))
      | ~ v1_relat_1(k2_funct_1(A_277))
      | ~ v2_funct_1(A_277)
      | ~ v1_funct_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2784])).

tff(c_3553,plain,(
    ! [A_9] :
      ( k1_relat_1(k6_relat_1(k2_relat_1(A_9))) = k1_relat_1(k2_funct_1(A_9))
      | ~ v2_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(k2_funct_1(A_9))
      | ~ v1_relat_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3532])).

tff(c_3745,plain,(
    ! [A_291] :
      ( k1_relat_1(k2_funct_1(A_291)) = k2_relat_1(A_291)
      | ~ v2_funct_1(k2_funct_1(A_291))
      | ~ v1_funct_1(k2_funct_1(A_291))
      | ~ v1_relat_1(k2_funct_1(A_291))
      | ~ v2_funct_1(A_291)
      | ~ v1_funct_1(A_291)
      | ~ v1_relat_1(A_291)
      | ~ v2_funct_1(A_291)
      | ~ v1_funct_1(A_291)
      | ~ v1_relat_1(A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3553])).

tff(c_3748,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3739,c_3745])).

tff(c_3760,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2964,c_2895,c_3136,c_3119,c_3487,c_3265,c_3748])).

tff(c_3762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3694,c_3760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.15  
% 5.87/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.87/2.16  
% 5.87/2.16  %Foreground sorts:
% 5.87/2.16  
% 5.87/2.16  
% 5.87/2.16  %Background operators:
% 5.87/2.16  
% 5.87/2.16  
% 5.87/2.16  %Foreground operators:
% 5.87/2.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.87/2.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.87/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.87/2.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.87/2.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.87/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.87/2.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.87/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.87/2.16  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.87/2.16  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.87/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.87/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.87/2.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.87/2.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.87/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.87/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.87/2.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.87/2.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.87/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.87/2.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.87/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.87/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.87/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.87/2.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.87/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.87/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.87/2.16  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.87/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.87/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.87/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.87/2.16  
% 5.87/2.19  tff(f_203, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 5.87/2.19  tff(f_159, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.87/2.19  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.87/2.19  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.87/2.19  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.87/2.19  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.87/2.19  tff(f_139, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 5.87/2.19  tff(f_131, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.87/2.19  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.87/2.19  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.87/2.19  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.87/2.19  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.87/2.19  tff(f_57, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 5.87/2.19  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 5.87/2.19  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.87/2.19  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.87/2.19  tff(f_111, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.87/2.19  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 5.87/2.19  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 5.87/2.19  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.87/2.19  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.87/2.19  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_82, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_101, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.87/2.19  tff(c_109, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_101])).
% 5.87/2.19  tff(c_78, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_108, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_101])).
% 5.87/2.19  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_136, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_72])).
% 5.87/2.19  tff(c_2451, plain, (![A_201, B_202, C_203]: (k2_relset_1(A_201, B_202, C_203)=k2_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.87/2.19  tff(c_2455, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_2451])).
% 5.87/2.19  tff(c_70, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_154, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_70])).
% 5.87/2.19  tff(c_2456, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_154])).
% 5.87/2.19  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_120, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.87/2.19  tff(c_126, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_108, c_120])).
% 5.87/2.19  tff(c_130, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_126])).
% 5.87/2.19  tff(c_131, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_130])).
% 5.87/2.19  tff(c_2465, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_131])).
% 5.87/2.19  tff(c_32, plain, (![C_13, A_11, B_12]: (v1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.87/2.19  tff(c_140, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_32])).
% 5.87/2.19  tff(c_179, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.87/2.19  tff(c_183, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_136, c_179])).
% 5.87/2.19  tff(c_2442, plain, (![B_198, A_199]: (k1_relat_1(B_198)=A_199 | ~v1_partfun1(B_198, A_199) | ~v4_relat_1(B_198, A_199) | ~v1_relat_1(B_198))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.87/2.19  tff(c_2445, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_183, c_2442])).
% 5.87/2.19  tff(c_2448, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2445])).
% 5.87/2.19  tff(c_2449, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2448])).
% 5.87/2.19  tff(c_74, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_114, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_74])).
% 5.87/2.19  tff(c_115, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_114])).
% 5.87/2.19  tff(c_2466, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_115])).
% 5.87/2.19  tff(c_2464, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_136])).
% 5.87/2.19  tff(c_2627, plain, (![C_221, A_222, B_223]: (v1_partfun1(C_221, A_222) | ~v1_funct_2(C_221, A_222, B_223) | ~v1_funct_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | v1_xboole_0(B_223))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.87/2.19  tff(c_2630, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2464, c_2627])).
% 5.87/2.19  tff(c_2633, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2466, c_2630])).
% 5.87/2.19  tff(c_2635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2465, c_2449, c_2633])).
% 5.87/2.19  tff(c_2636, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2448])).
% 5.87/2.19  tff(c_2642, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_136])).
% 5.87/2.19  tff(c_38, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.87/2.19  tff(c_2690, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2642, c_38])).
% 5.87/2.19  tff(c_2641, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_154])).
% 5.87/2.19  tff(c_2697, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2690, c_2641])).
% 5.87/2.19  tff(c_2644, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_115])).
% 5.87/2.19  tff(c_2704, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2697, c_2644])).
% 5.87/2.19  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_2702, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2697, c_2690])).
% 5.87/2.19  tff(c_2703, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2697, c_2642])).
% 5.87/2.19  tff(c_3061, plain, (![C_268, B_269, A_270]: (m1_subset_1(k2_funct_1(C_268), k1_zfmisc_1(k2_zfmisc_1(B_269, A_270))) | k2_relset_1(A_270, B_269, C_268)!=B_269 | ~v2_funct_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_270, B_269))) | ~v1_funct_2(C_268, A_270, B_269) | ~v1_funct_1(C_268))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.87/2.19  tff(c_3683, plain, (![B_287, A_288, C_289]: (k2_relset_1(B_287, A_288, k2_funct_1(C_289))=k2_relat_1(k2_funct_1(C_289)) | k2_relset_1(A_288, B_287, C_289)!=B_287 | ~v2_funct_1(C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))) | ~v1_funct_2(C_289, A_288, B_287) | ~v1_funct_1(C_289))), inference(resolution, [status(thm)], [c_3061, c_38])).
% 5.87/2.19  tff(c_3689, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2703, c_3683])).
% 5.87/2.19  tff(c_3693, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2704, c_68, c_2702, c_3689])).
% 5.87/2.19  tff(c_2965, plain, (![A_262, B_263, C_264]: (k2_tops_2(A_262, B_263, C_264)=k2_funct_1(C_264) | ~v2_funct_1(C_264) | k2_relset_1(A_262, B_263, C_264)!=B_263 | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~v1_funct_2(C_264, A_262, B_263) | ~v1_funct_1(C_264))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.87/2.19  tff(c_2968, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2703, c_2965])).
% 5.87/2.19  tff(c_2971, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2704, c_2702, c_68, c_2968])).
% 5.87/2.19  tff(c_225, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.87/2.19  tff(c_229, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_225])).
% 5.87/2.19  tff(c_230, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_154])).
% 5.87/2.19  tff(c_238, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_131])).
% 5.87/2.19  tff(c_218, plain, (![B_67, A_68]: (k1_relat_1(B_67)=A_68 | ~v1_partfun1(B_67, A_68) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.87/2.19  tff(c_221, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_183, c_218])).
% 5.87/2.19  tff(c_224, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_221])).
% 5.87/2.19  tff(c_278, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_224])).
% 5.87/2.19  tff(c_239, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_115])).
% 5.87/2.19  tff(c_237, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_136])).
% 5.87/2.19  tff(c_398, plain, (![C_90, A_91, B_92]: (v1_partfun1(C_90, A_91) | ~v1_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | v1_xboole_0(B_92))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.87/2.19  tff(c_401, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_237, c_398])).
% 5.87/2.19  tff(c_404, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_239, c_401])).
% 5.87/2.19  tff(c_406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_278, c_404])).
% 5.87/2.19  tff(c_407, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_224])).
% 5.87/2.19  tff(c_411, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_239])).
% 5.87/2.19  tff(c_267, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_237, c_38])).
% 5.87/2.19  tff(c_454, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_267])).
% 5.87/2.19  tff(c_410, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_237])).
% 5.87/2.19  tff(c_780, plain, (![A_134, B_135, C_136]: (k2_tops_2(A_134, B_135, C_136)=k2_funct_1(C_136) | ~v2_funct_1(C_136) | k2_relset_1(A_134, B_135, C_136)!=B_135 | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(C_136, A_134, B_135) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.87/2.19  tff(c_783, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_410, c_780])).
% 5.87/2.19  tff(c_786, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_411, c_454, c_68, c_783])).
% 5.87/2.19  tff(c_66, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.87/2.19  tff(c_184, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_109, c_108, c_108, c_109, c_109, c_108, c_108, c_66])).
% 5.87/2.19  tff(c_185, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_184])).
% 5.87/2.19  tff(c_459, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_407, c_230, c_230, c_230, c_185])).
% 5.87/2.19  tff(c_787, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_786, c_459])).
% 5.87/2.19  tff(c_30, plain, (![A_10]: (k2_funct_1(k2_funct_1(A_10))=A_10 | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.87/2.19  tff(c_12, plain, (![A_4]: (v1_relat_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.87/2.19  tff(c_606, plain, (![C_115, A_116, B_117]: (v1_funct_1(k2_funct_1(C_115)) | k2_relset_1(A_116, B_117, C_115)!=B_117 | ~v2_funct_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(C_115, A_116, B_117) | ~v1_funct_1(C_115))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.87/2.19  tff(c_609, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_410, c_606])).
% 5.87/2.19  tff(c_612, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_411, c_68, c_454, c_609])).
% 5.87/2.19  tff(c_14, plain, (![A_5]: (v2_funct_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.87/2.19  tff(c_535, plain, (![B_98, A_99]: (k9_relat_1(k2_funct_1(B_98), A_99)=k10_relat_1(B_98, A_99) | ~v2_funct_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.87/2.19  tff(c_613, plain, (![A_118, A_119]: (k10_relat_1(k2_funct_1(A_118), A_119)=k9_relat_1(A_118, A_119) | ~v2_funct_1(k2_funct_1(A_118)) | ~v1_funct_1(k2_funct_1(A_118)) | ~v1_relat_1(k2_funct_1(A_118)) | ~v2_funct_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_30, c_535])).
% 5.87/2.19  tff(c_626, plain, (![A_123, A_124]: (k10_relat_1(k2_funct_1(A_123), A_124)=k9_relat_1(A_123, A_124) | ~v1_funct_1(k2_funct_1(A_123)) | ~v1_relat_1(k2_funct_1(A_123)) | ~v2_funct_1(A_123) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_14, c_613])).
% 5.87/2.19  tff(c_632, plain, (![A_125, A_126]: (k10_relat_1(k2_funct_1(A_125), A_126)=k9_relat_1(A_125, A_126) | ~v1_funct_1(k2_funct_1(A_125)) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(resolution, [status(thm)], [c_12, c_626])).
% 5.87/2.19  tff(c_634, plain, (![A_126]: (k10_relat_1(k2_funct_1('#skF_3'), A_126)=k9_relat_1('#skF_3', A_126) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_612, c_632])).
% 5.87/2.19  tff(c_643, plain, (![A_127]: (k10_relat_1(k2_funct_1('#skF_3'), A_127)=k9_relat_1('#skF_3', A_127))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_634])).
% 5.87/2.19  tff(c_4, plain, (![A_2]: (k10_relat_1(A_2, k2_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.87/2.19  tff(c_654, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_643, c_4])).
% 5.87/2.19  tff(c_672, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_654])).
% 5.87/2.19  tff(c_682, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_672])).
% 5.87/2.19  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_682])).
% 5.87/2.19  tff(c_688, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_654])).
% 5.87/2.19  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.87/2.19  tff(c_542, plain, (![B_98]: (k10_relat_1(B_98, k1_relat_1(k2_funct_1(B_98)))=k2_relat_1(k2_funct_1(B_98)) | ~v1_relat_1(k2_funct_1(B_98)) | ~v2_funct_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(superposition, [status(thm), theory('equality')], [c_535, c_2])).
% 5.87/2.19  tff(c_650, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_643, c_542])).
% 5.87/2.19  tff(c_668, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_650])).
% 5.87/2.19  tff(c_769, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_668])).
% 5.87/2.19  tff(c_770, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_769])).
% 5.87/2.19  tff(c_773, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_770])).
% 5.87/2.19  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_773])).
% 5.87/2.19  tff(c_779, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_769])).
% 5.87/2.19  tff(c_661, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_542, c_643])).
% 5.87/2.19  tff(c_671, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_661])).
% 5.87/2.19  tff(c_793, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_779, c_671])).
% 5.87/2.19  tff(c_794, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_793])).
% 5.87/2.19  tff(c_797, plain, (~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_794])).
% 5.87/2.19  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_140, c_797])).
% 5.87/2.19  tff(c_804, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_793])).
% 5.87/2.19  tff(c_815, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_804])).
% 5.87/2.19  tff(c_819, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_815])).
% 5.87/2.19  tff(c_831, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_819])).
% 5.87/2.19  tff(c_839, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_831])).
% 5.87/2.19  tff(c_641, plain, (![A_126]: (k10_relat_1(k2_funct_1('#skF_3'), A_126)=k9_relat_1('#skF_3', A_126))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_634])).
% 5.87/2.19  tff(c_857, plain, (![C_137, B_138, A_139]: (m1_subset_1(k2_funct_1(C_137), k1_zfmisc_1(k2_zfmisc_1(B_138, A_139))) | k2_relset_1(A_139, B_138, C_137)!=B_138 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_2(C_137, A_139, B_138) | ~v1_funct_1(C_137))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.87/2.19  tff(c_40, plain, (![A_20, B_21, C_22, D_23]: (k8_relset_1(A_20, B_21, C_22, D_23)=k10_relat_1(C_22, D_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.87/2.19  tff(c_2097, plain, (![B_179, A_180, C_181, D_182]: (k8_relset_1(B_179, A_180, k2_funct_1(C_181), D_182)=k10_relat_1(k2_funct_1(C_181), D_182) | k2_relset_1(A_180, B_179, C_181)!=B_179 | ~v2_funct_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_180, B_179))) | ~v1_funct_2(C_181, A_180, B_179) | ~v1_funct_1(C_181))), inference(resolution, [status(thm)], [c_857, c_40])).
% 5.87/2.19  tff(c_2101, plain, (![D_182]: (k8_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'), D_182)=k10_relat_1(k2_funct_1('#skF_3'), D_182) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_410, c_2097])).
% 5.87/2.19  tff(c_2105, plain, (![D_182]: (k8_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'), D_182)=k9_relat_1('#skF_3', D_182))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_411, c_68, c_454, c_641, c_2101])).
% 5.87/2.19  tff(c_42, plain, (![A_24, B_25, C_26]: (k8_relset_1(A_24, B_25, C_26, B_25)=k1_relset_1(A_24, B_25, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.87/2.19  tff(c_2393, plain, (![B_192, A_193, C_194]: (k8_relset_1(B_192, A_193, k2_funct_1(C_194), A_193)=k1_relset_1(B_192, A_193, k2_funct_1(C_194)) | k2_relset_1(A_193, B_192, C_194)!=B_192 | ~v2_funct_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))) | ~v1_funct_2(C_194, A_193, B_192) | ~v1_funct_1(C_194))), inference(resolution, [status(thm)], [c_857, c_42])).
% 5.87/2.19  tff(c_2397, plain, (k8_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))=k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_410, c_2393])).
% 5.87/2.19  tff(c_2401, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_411, c_68, c_454, c_839, c_2105, c_2397])).
% 5.87/2.19  tff(c_2403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_787, c_2401])).
% 5.87/2.19  tff(c_2404, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 5.87/2.19  tff(c_2638, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_2636, c_2636, c_2404])).
% 5.87/2.19  tff(c_2850, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2697, c_2697, c_2638])).
% 5.87/2.19  tff(c_2972, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2971, c_2850])).
% 5.87/2.19  tff(c_3694, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3693, c_2972])).
% 5.87/2.19  tff(c_2889, plain, (![C_249, A_250, B_251]: (v1_funct_1(k2_funct_1(C_249)) | k2_relset_1(A_250, B_251, C_249)!=B_251 | ~v2_funct_1(C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_funct_2(C_249, A_250, B_251) | ~v1_funct_1(C_249))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.87/2.19  tff(c_2892, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2703, c_2889])).
% 5.87/2.19  tff(c_2895, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2704, c_68, c_2702, c_2892])).
% 5.87/2.19  tff(c_2722, plain, (![B_227, A_228]: (k9_relat_1(k2_funct_1(B_227), A_228)=k10_relat_1(B_227, A_228) | ~v2_funct_1(B_227) | ~v1_funct_1(B_227) | ~v1_relat_1(B_227))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.87/2.19  tff(c_2896, plain, (![A_252, A_253]: (k10_relat_1(k2_funct_1(A_252), A_253)=k9_relat_1(A_252, A_253) | ~v2_funct_1(k2_funct_1(A_252)) | ~v1_funct_1(k2_funct_1(A_252)) | ~v1_relat_1(k2_funct_1(A_252)) | ~v2_funct_1(A_252) | ~v1_funct_1(A_252) | ~v1_relat_1(A_252))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2722])).
% 5.87/2.19  tff(c_2902, plain, (![A_254, A_255]: (k10_relat_1(k2_funct_1(A_254), A_255)=k9_relat_1(A_254, A_255) | ~v1_funct_1(k2_funct_1(A_254)) | ~v1_relat_1(k2_funct_1(A_254)) | ~v2_funct_1(A_254) | ~v1_funct_1(A_254) | ~v1_relat_1(A_254))), inference(resolution, [status(thm)], [c_14, c_2896])).
% 5.87/2.19  tff(c_2915, plain, (![A_259, A_260]: (k10_relat_1(k2_funct_1(A_259), A_260)=k9_relat_1(A_259, A_260) | ~v1_funct_1(k2_funct_1(A_259)) | ~v2_funct_1(A_259) | ~v1_funct_1(A_259) | ~v1_relat_1(A_259))), inference(resolution, [status(thm)], [c_12, c_2902])).
% 5.87/2.19  tff(c_2917, plain, (![A_260]: (k10_relat_1(k2_funct_1('#skF_3'), A_260)=k9_relat_1('#skF_3', A_260) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2895, c_2915])).
% 5.87/2.19  tff(c_2926, plain, (![A_261]: (k10_relat_1(k2_funct_1('#skF_3'), A_261)=k9_relat_1('#skF_3', A_261))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_2917])).
% 5.87/2.19  tff(c_2937, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2926, c_4])).
% 5.87/2.19  tff(c_2955, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2937])).
% 5.87/2.19  tff(c_2958, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_2955])).
% 5.87/2.19  tff(c_2962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_2958])).
% 5.87/2.19  tff(c_2964, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2937])).
% 5.87/2.19  tff(c_2739, plain, (![B_227]: (k10_relat_1(B_227, k1_relat_1(k2_funct_1(B_227)))=k2_relat_1(k2_funct_1(B_227)) | ~v2_funct_1(B_227) | ~v1_funct_1(B_227) | ~v1_relat_1(B_227) | ~v1_relat_1(k2_funct_1(B_227)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2722])).
% 5.87/2.19  tff(c_2944, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2739, c_2926])).
% 5.87/2.19  tff(c_2954, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2895, c_2944])).
% 5.87/2.19  tff(c_3107, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2964, c_2954])).
% 5.87/2.19  tff(c_3108, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3107])).
% 5.87/2.19  tff(c_3111, plain, (~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3108])).
% 5.87/2.19  tff(c_3117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_140, c_3111])).
% 5.87/2.19  tff(c_3119, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3107])).
% 5.87/2.19  tff(c_2933, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2926, c_2739])).
% 5.87/2.19  tff(c_2951, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2895, c_2933])).
% 5.87/2.19  tff(c_3126, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_2964, c_2951])).
% 5.87/2.19  tff(c_3127, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3126])).
% 5.87/2.19  tff(c_3130, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_3127])).
% 5.87/2.19  tff(c_3134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_3130])).
% 5.87/2.19  tff(c_3136, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3126])).
% 5.87/2.19  tff(c_3135, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3126])).
% 5.87/2.19  tff(c_3141, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3135])).
% 5.87/2.19  tff(c_3145, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_3141])).
% 5.87/2.19  tff(c_3157, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3145])).
% 5.87/2.19  tff(c_3165, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_3157])).
% 5.87/2.19  tff(c_3166, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_3145])).
% 5.87/2.19  tff(c_10, plain, (![A_4]: (v1_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.87/2.19  tff(c_2988, plain, (![A_265, A_266]: (k10_relat_1(k2_funct_1(A_265), A_266)=k9_relat_1(A_265, A_266) | ~v2_funct_1(A_265) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(resolution, [status(thm)], [c_10, c_2915])).
% 5.87/2.19  tff(c_3003, plain, (![A_265]: (k9_relat_1(A_265, k2_relat_1(k2_funct_1(A_265)))=k1_relat_1(k2_funct_1(A_265)) | ~v1_relat_1(k2_funct_1(A_265)) | ~v2_funct_1(A_265) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(superposition, [status(thm), theory('equality')], [c_2988, c_4])).
% 5.87/2.19  tff(c_3197, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3166, c_3003])).
% 5.87/2.19  tff(c_3207, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2964, c_2895, c_3136, c_3119, c_3197])).
% 5.87/2.19  tff(c_20, plain, (![B_7, A_6]: (k9_relat_1(k2_funct_1(B_7), A_6)=k10_relat_1(B_7, A_6) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.87/2.19  tff(c_3217, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k10_relat_1('#skF_3', k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3207, c_20])).
% 5.87/2.19  tff(c_3224, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k10_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_3217])).
% 5.87/2.19  tff(c_3242, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3224])).
% 5.87/2.19  tff(c_3252, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_3242])).
% 5.87/2.19  tff(c_3265, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3252, c_3224])).
% 5.87/2.19  tff(c_2806, plain, (![A_232]: (k2_relat_1(k5_relat_1(A_232, k2_funct_1(A_232)))=k1_relat_1(A_232) | ~v2_funct_1(A_232) | ~v1_funct_1(A_232) | ~v1_relat_1(A_232))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.87/2.19  tff(c_3315, plain, (![A_274]: (k10_relat_1(k5_relat_1(A_274, k2_funct_1(A_274)), k1_relat_1(A_274))=k1_relat_1(k5_relat_1(A_274, k2_funct_1(A_274))) | ~v1_relat_1(k5_relat_1(A_274, k2_funct_1(A_274))) | ~v2_funct_1(A_274) | ~v1_funct_1(A_274) | ~v1_relat_1(A_274))), inference(superposition, [status(thm), theory('equality')], [c_2806, c_4])).
% 5.87/2.19  tff(c_3324, plain, (k10_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), k1_relat_1('#skF_3'))=k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3265, c_3315])).
% 5.87/2.19  tff(c_3340, plain, (k10_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), k1_relat_1('#skF_3'))=k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_3324])).
% 5.87/2.19  tff(c_3476, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3340])).
% 5.87/2.19  tff(c_3479, plain, (~v1_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3476])).
% 5.87/2.19  tff(c_3485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_76, c_3479])).
% 5.87/2.19  tff(c_3487, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3340])).
% 5.87/2.19  tff(c_2784, plain, (![A_231]: (k1_relat_1(k5_relat_1(A_231, k2_funct_1(A_231)))=k1_relat_1(A_231) | ~v2_funct_1(A_231) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.87/2.19  tff(c_3613, plain, (![A_285]: (k9_relat_1(k5_relat_1(A_285, k2_funct_1(A_285)), k1_relat_1(A_285))=k2_relat_1(k5_relat_1(A_285, k2_funct_1(A_285))) | ~v1_relat_1(k5_relat_1(A_285, k2_funct_1(A_285))) | ~v2_funct_1(A_285) | ~v1_funct_1(A_285) | ~v1_relat_1(A_285))), inference(superposition, [status(thm), theory('equality')], [c_2784, c_2])).
% 5.87/2.19  tff(c_3628, plain, (k9_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), k1_relat_1('#skF_3'))=k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3265, c_3613])).
% 5.87/2.19  tff(c_3644, plain, (k9_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), k1_relat_1('#skF_3'))=k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_3487, c_3628])).
% 5.87/2.19  tff(c_3728, plain, (~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3644])).
% 5.87/2.19  tff(c_3731, plain, (~v2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3728])).
% 5.87/2.19  tff(c_3737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_76, c_68, c_68, c_3731])).
% 5.87/2.19  tff(c_3739, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3644])).
% 5.87/2.19  tff(c_6, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.87/2.19  tff(c_26, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_relat_1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.87/2.19  tff(c_3532, plain, (![A_277]: (k1_relat_1(k5_relat_1(k2_funct_1(A_277), A_277))=k1_relat_1(k2_funct_1(A_277)) | ~v2_funct_1(k2_funct_1(A_277)) | ~v1_funct_1(k2_funct_1(A_277)) | ~v1_relat_1(k2_funct_1(A_277)) | ~v2_funct_1(A_277) | ~v1_funct_1(A_277) | ~v1_relat_1(A_277))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2784])).
% 5.87/2.19  tff(c_3553, plain, (![A_9]: (k1_relat_1(k6_relat_1(k2_relat_1(A_9)))=k1_relat_1(k2_funct_1(A_9)) | ~v2_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(k2_funct_1(A_9)) | ~v1_relat_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3532])).
% 5.87/2.19  tff(c_3745, plain, (![A_291]: (k1_relat_1(k2_funct_1(A_291))=k2_relat_1(A_291) | ~v2_funct_1(k2_funct_1(A_291)) | ~v1_funct_1(k2_funct_1(A_291)) | ~v1_relat_1(k2_funct_1(A_291)) | ~v2_funct_1(A_291) | ~v1_funct_1(A_291) | ~v1_relat_1(A_291) | ~v2_funct_1(A_291) | ~v1_funct_1(A_291) | ~v1_relat_1(A_291))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3553])).
% 5.87/2.19  tff(c_3748, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3739, c_3745])).
% 5.87/2.19  tff(c_3760, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2964, c_2895, c_3136, c_3119, c_3487, c_3265, c_3748])).
% 5.87/2.19  tff(c_3762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3694, c_3760])).
% 5.87/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.19  
% 5.87/2.19  Inference rules
% 5.87/2.19  ----------------------
% 5.87/2.19  #Ref     : 0
% 5.87/2.19  #Sup     : 893
% 5.87/2.19  #Fact    : 0
% 5.87/2.19  #Define  : 0
% 5.87/2.19  #Split   : 21
% 5.87/2.19  #Chain   : 0
% 5.87/2.19  #Close   : 0
% 5.87/2.19  
% 5.87/2.19  Ordering : KBO
% 5.87/2.19  
% 5.87/2.19  Simplification rules
% 5.87/2.19  ----------------------
% 5.87/2.19  #Subsume      : 40
% 5.87/2.19  #Demod        : 1028
% 5.87/2.19  #Tautology    : 466
% 5.87/2.19  #SimpNegUnit  : 11
% 5.87/2.19  #BackRed      : 57
% 5.87/2.19  
% 5.87/2.19  #Partial instantiations: 0
% 5.87/2.19  #Strategies tried      : 1
% 5.87/2.19  
% 5.87/2.19  Timing (in seconds)
% 5.87/2.19  ----------------------
% 5.87/2.19  Preprocessing        : 0.38
% 5.87/2.19  Parsing              : 0.21
% 5.87/2.19  CNF conversion       : 0.02
% 5.87/2.19  Main loop            : 0.95
% 5.87/2.19  Inferencing          : 0.33
% 5.87/2.19  Reduction            : 0.35
% 5.87/2.19  Demodulation         : 0.26
% 5.87/2.19  BG Simplification    : 0.05
% 5.87/2.19  Subsumption          : 0.15
% 5.87/2.19  Abstraction          : 0.05
% 5.87/2.19  MUC search           : 0.00
% 5.87/2.19  Cooper               : 0.00
% 5.87/2.19  Total                : 1.40
% 5.87/2.19  Index Insertion      : 0.00
% 5.87/2.20  Index Deletion       : 0.00
% 5.87/2.20  Index Matching       : 0.00
% 5.87/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
