%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:25 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  157 (10466 expanded)
%              Number of leaves         :   41 (3662 expanded)
%              Depth                    :   23
%              Number of atoms          :  306 (31542 expanded)
%              Number of equality atoms :   74 (9908 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_146,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_60,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_60])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_67,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_94,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_48])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_100,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_943,plain,(
    ! [A_108] :
      ( m1_subset_1(A_108,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_108),k2_relat_1(A_108))))
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1153,plain,(
    ! [A_129] :
      ( m1_subset_1(k2_funct_1(A_129),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_129),k2_relat_1(k2_funct_1(A_129)))))
      | ~ v1_funct_1(k2_funct_1(A_129))
      | ~ v1_relat_1(k2_funct_1(A_129))
      | ~ v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_943])).

tff(c_1346,plain,(
    ! [A_139] :
      ( m1_subset_1(k2_funct_1(A_139),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_139),k1_relat_1(A_139))))
      | ~ v1_funct_1(k2_funct_1(A_139))
      | ~ v1_relat_1(k2_funct_1(A_139))
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139)
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1153])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1383,plain,(
    ! [A_140] :
      ( k1_relset_1(k2_relat_1(A_140),k1_relat_1(A_140),k2_funct_1(A_140)) = k1_relat_1(k2_funct_1(A_140))
      | ~ v1_funct_1(k2_funct_1(A_140))
      | ~ v1_relat_1(k2_funct_1(A_140))
      | ~ v2_funct_1(A_140)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_1346,c_18])).

tff(c_155,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_159,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_155])).

tff(c_46,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_101,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_46])).

tff(c_160,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_101])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_79,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_85,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_79])).

tff(c_89,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_85])).

tff(c_90,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_89])).

tff(c_168,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_90])).

tff(c_106,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_110,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_94,c_106])).

tff(c_133,plain,(
    ! [B_50,A_51] :
      ( k1_relat_1(B_50) = A_51
      | ~ v1_partfun1(B_50,A_51)
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_136,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_133])).

tff(c_139,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_136])).

tff(c_140,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_77,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_50])).

tff(c_169,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_77])).

tff(c_167,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_94])).

tff(c_300,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_partfun1(C_65,A_66)
      | ~ v1_funct_2(C_65,A_66,B_67)
      | ~ v1_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | v1_xboole_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_303,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_167,c_300])).

tff(c_309,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_169,c_303])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_140,c_309])).

tff(c_312,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_316,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_94])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_905,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_316,c_20])).

tff(c_315,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_101])).

tff(c_917,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_315])).

tff(c_318,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_77])).

tff(c_925,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_318])).

tff(c_922,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_905])).

tff(c_924,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_316])).

tff(c_1128,plain,(
    ! [A_125,B_126,C_127] :
      ( k2_tops_2(A_125,B_126,C_127) = k2_funct_1(C_127)
      | ~ v2_funct_1(C_127)
      | k2_relset_1(A_125,B_126,C_127) != B_126
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(C_127,A_125,B_126)
      | ~ v1_funct_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1131,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_924,c_1128])).

tff(c_1137,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_925,c_922,c_44,c_1131])).

tff(c_6,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_392,plain,(
    ! [A_72] :
      ( m1_subset_1(A_72,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_72),k2_relat_1(A_72))))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_650,plain,(
    ! [A_94] :
      ( m1_subset_1(k2_funct_1(A_94),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_94)),k1_relat_1(A_94))))
      | ~ v1_funct_1(k2_funct_1(A_94))
      | ~ v1_relat_1(k2_funct_1(A_94))
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_392])).

tff(c_806,plain,(
    ! [A_103] :
      ( m1_subset_1(k2_funct_1(A_103),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_103),k1_relat_1(A_103))))
      | ~ v1_funct_1(k2_funct_1(A_103))
      | ~ v1_relat_1(k2_funct_1(A_103))
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103)
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_650])).

tff(c_843,plain,(
    ! [A_104] :
      ( k1_relset_1(k2_relat_1(A_104),k1_relat_1(A_104),k2_funct_1(A_104)) = k1_relat_1(k2_funct_1(A_104))
      | ~ v1_funct_1(k2_funct_1(A_104))
      | ~ v1_relat_1(k2_funct_1(A_104))
      | ~ v2_funct_1(A_104)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_806,c_18])).

tff(c_382,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_386,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_316,c_382])).

tff(c_387,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_315])).

tff(c_419,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_318])).

tff(c_417,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_386])).

tff(c_418,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_316])).

tff(c_575,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_tops_2(A_86,B_87,C_88) = k2_funct_1(C_88)
      | ~ v2_funct_1(C_88)
      | k2_relset_1(A_86,B_87,C_88) != B_87
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(C_88,A_86,B_87)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_578,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_418,c_575])).

tff(c_584,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_419,c_417,c_44,c_578])).

tff(c_319,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_68])).

tff(c_42,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_360,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3')
    | k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_319,c_67,c_67,c_319,c_319,c_312,c_67,c_67,c_42])).

tff(c_361,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_496,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_387,c_387,c_361])).

tff(c_586,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_496])).

tff(c_849,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_586])).

tff(c_861,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_44,c_849])).

tff(c_863,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_861])).

tff(c_866,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_863])).

tff(c_870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_866])).

tff(c_871,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_861])).

tff(c_873,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_871])).

tff(c_876,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_873])).

tff(c_880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_44,c_876])).

tff(c_881,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_871])).

tff(c_885,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_881])).

tff(c_889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_885])).

tff(c_891,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_985,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_917,c_917,c_891])).

tff(c_1140,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_985])).

tff(c_1389,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1383,c_1140])).

tff(c_1404,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_44,c_1389])).

tff(c_1408,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_1411,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1408])).

tff(c_1415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_1411])).

tff(c_1417,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1416,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1424,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1416])).

tff(c_1427,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1424])).

tff(c_1431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_1427])).

tff(c_1433,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1416])).

tff(c_1432,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1416])).

tff(c_1044,plain,(
    ! [A_118] :
      ( k2_relset_1(k1_relat_1(A_118),k2_relat_1(A_118),A_118) = k2_relat_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_943,c_20])).

tff(c_1059,plain,(
    ! [A_7] :
      ( k2_relset_1(k1_relat_1(k2_funct_1(A_7)),k1_relat_1(A_7),k2_funct_1(A_7)) = k2_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1044])).

tff(c_1446,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_1059])).

tff(c_1513,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_44,c_1417,c_1433,c_1446])).

tff(c_890,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_923,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_917,c_890])).

tff(c_1139,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_923])).

tff(c_1657,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1513,c_1139])).

tff(c_1664,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1657])).

tff(c_1668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52,c_44,c_1664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:04:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.69  
% 3.81/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.81/1.69  
% 3.81/1.69  %Foreground sorts:
% 3.81/1.69  
% 3.81/1.69  
% 3.81/1.69  %Background operators:
% 3.81/1.69  
% 3.81/1.69  
% 3.81/1.69  %Foreground operators:
% 3.81/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.81/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.81/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.81/1.69  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.81/1.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.81/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.81/1.69  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.81/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.81/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.69  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.81/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.81/1.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.81/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.81/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.81/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.81/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.81/1.69  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.81/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.81/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.69  
% 4.05/1.71  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.05/1.71  tff(f_146, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 4.05/1.71  tff(f_102, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.05/1.71  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.05/1.71  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.05/1.71  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.05/1.71  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.05/1.71  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.05/1.71  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.05/1.71  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.05/1.71  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.05/1.71  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.05/1.71  tff(f_80, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.05/1.71  tff(f_122, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.05/1.71  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.05/1.71  tff(c_58, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_60, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.05/1.71  tff(c_68, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_60])).
% 4.05/1.71  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_67, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_60])).
% 4.05/1.71  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_94, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_48])).
% 4.05/1.71  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.05/1.71  tff(c_97, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_94, c_2])).
% 4.05/1.71  tff(c_100, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_97])).
% 4.05/1.71  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_10, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.05/1.71  tff(c_8, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.05/1.71  tff(c_12, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.05/1.71  tff(c_943, plain, (![A_108]: (m1_subset_1(A_108, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_108), k2_relat_1(A_108)))) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.05/1.71  tff(c_1153, plain, (![A_129]: (m1_subset_1(k2_funct_1(A_129), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_129), k2_relat_1(k2_funct_1(A_129))))) | ~v1_funct_1(k2_funct_1(A_129)) | ~v1_relat_1(k2_funct_1(A_129)) | ~v2_funct_1(A_129) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(superposition, [status(thm), theory('equality')], [c_12, c_943])).
% 4.05/1.71  tff(c_1346, plain, (![A_139]: (m1_subset_1(k2_funct_1(A_139), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_139), k1_relat_1(A_139)))) | ~v1_funct_1(k2_funct_1(A_139)) | ~v1_relat_1(k2_funct_1(A_139)) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1153])).
% 4.05/1.71  tff(c_18, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.05/1.71  tff(c_1383, plain, (![A_140]: (k1_relset_1(k2_relat_1(A_140), k1_relat_1(A_140), k2_funct_1(A_140))=k1_relat_1(k2_funct_1(A_140)) | ~v1_funct_1(k2_funct_1(A_140)) | ~v1_relat_1(k2_funct_1(A_140)) | ~v2_funct_1(A_140) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_1346, c_18])).
% 4.05/1.71  tff(c_155, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.05/1.71  tff(c_159, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_155])).
% 4.05/1.71  tff(c_46, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_101, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_46])).
% 4.05/1.71  tff(c_160, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_101])).
% 4.05/1.71  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_79, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.05/1.71  tff(c_85, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_67, c_79])).
% 4.05/1.71  tff(c_89, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_85])).
% 4.05/1.71  tff(c_90, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_89])).
% 4.05/1.71  tff(c_168, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_90])).
% 4.05/1.71  tff(c_106, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.05/1.71  tff(c_110, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_94, c_106])).
% 4.05/1.71  tff(c_133, plain, (![B_50, A_51]: (k1_relat_1(B_50)=A_51 | ~v1_partfun1(B_50, A_51) | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.05/1.71  tff(c_136, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_110, c_133])).
% 4.05/1.71  tff(c_139, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_136])).
% 4.05/1.71  tff(c_140, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 4.05/1.71  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_77, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_50])).
% 4.05/1.71  tff(c_169, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_77])).
% 4.05/1.71  tff(c_167, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_94])).
% 4.05/1.71  tff(c_300, plain, (![C_65, A_66, B_67]: (v1_partfun1(C_65, A_66) | ~v1_funct_2(C_65, A_66, B_67) | ~v1_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | v1_xboole_0(B_67))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.05/1.71  tff(c_303, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_167, c_300])).
% 4.05/1.71  tff(c_309, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_169, c_303])).
% 4.05/1.71  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_140, c_309])).
% 4.05/1.71  tff(c_312, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_139])).
% 4.05/1.71  tff(c_316, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_94])).
% 4.05/1.71  tff(c_20, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.05/1.71  tff(c_905, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_316, c_20])).
% 4.05/1.71  tff(c_315, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_101])).
% 4.05/1.71  tff(c_917, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_905, c_315])).
% 4.05/1.71  tff(c_318, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_77])).
% 4.05/1.71  tff(c_925, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_318])).
% 4.05/1.71  tff(c_922, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_917, c_905])).
% 4.05/1.71  tff(c_924, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_316])).
% 4.05/1.71  tff(c_1128, plain, (![A_125, B_126, C_127]: (k2_tops_2(A_125, B_126, C_127)=k2_funct_1(C_127) | ~v2_funct_1(C_127) | k2_relset_1(A_125, B_126, C_127)!=B_126 | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(C_127, A_125, B_126) | ~v1_funct_1(C_127))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.05/1.71  tff(c_1131, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_924, c_1128])).
% 4.05/1.71  tff(c_1137, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_925, c_922, c_44, c_1131])).
% 4.05/1.71  tff(c_6, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.05/1.71  tff(c_392, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_72), k2_relat_1(A_72)))) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.05/1.71  tff(c_650, plain, (![A_94]: (m1_subset_1(k2_funct_1(A_94), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_94)), k1_relat_1(A_94)))) | ~v1_funct_1(k2_funct_1(A_94)) | ~v1_relat_1(k2_funct_1(A_94)) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_10, c_392])).
% 4.05/1.71  tff(c_806, plain, (![A_103]: (m1_subset_1(k2_funct_1(A_103), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_103), k1_relat_1(A_103)))) | ~v1_funct_1(k2_funct_1(A_103)) | ~v1_relat_1(k2_funct_1(A_103)) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_12, c_650])).
% 4.05/1.71  tff(c_843, plain, (![A_104]: (k1_relset_1(k2_relat_1(A_104), k1_relat_1(A_104), k2_funct_1(A_104))=k1_relat_1(k2_funct_1(A_104)) | ~v1_funct_1(k2_funct_1(A_104)) | ~v1_relat_1(k2_funct_1(A_104)) | ~v2_funct_1(A_104) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_806, c_18])).
% 4.05/1.71  tff(c_382, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.05/1.71  tff(c_386, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_316, c_382])).
% 4.05/1.71  tff(c_387, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_315])).
% 4.05/1.71  tff(c_419, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_318])).
% 4.05/1.71  tff(c_417, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_386])).
% 4.05/1.71  tff(c_418, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_316])).
% 4.05/1.71  tff(c_575, plain, (![A_86, B_87, C_88]: (k2_tops_2(A_86, B_87, C_88)=k2_funct_1(C_88) | ~v2_funct_1(C_88) | k2_relset_1(A_86, B_87, C_88)!=B_87 | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(C_88, A_86, B_87) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.05/1.71  tff(c_578, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_418, c_575])).
% 4.05/1.71  tff(c_584, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_419, c_417, c_44, c_578])).
% 4.05/1.71  tff(c_319, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_68])).
% 4.05/1.71  tff(c_42, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.05/1.71  tff(c_360, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3') | k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_319, c_67, c_67, c_319, c_319, c_312, c_67, c_67, c_42])).
% 4.05/1.71  tff(c_361, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_360])).
% 4.05/1.71  tff(c_496, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_387, c_387, c_361])).
% 4.05/1.71  tff(c_586, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_496])).
% 4.05/1.71  tff(c_849, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_843, c_586])).
% 4.05/1.71  tff(c_861, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_44, c_849])).
% 4.05/1.71  tff(c_863, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_861])).
% 4.05/1.71  tff(c_866, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_863])).
% 4.05/1.71  tff(c_870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_866])).
% 4.05/1.71  tff(c_871, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_861])).
% 4.05/1.71  tff(c_873, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_871])).
% 4.05/1.71  tff(c_876, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_873])).
% 4.05/1.71  tff(c_880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_44, c_876])).
% 4.05/1.71  tff(c_881, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_871])).
% 4.05/1.71  tff(c_885, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_881])).
% 4.05/1.71  tff(c_889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_885])).
% 4.05/1.72  tff(c_891, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_360])).
% 4.05/1.72  tff(c_985, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_917, c_917, c_917, c_891])).
% 4.05/1.72  tff(c_1140, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1137, c_985])).
% 4.05/1.72  tff(c_1389, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1383, c_1140])).
% 4.05/1.72  tff(c_1404, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_44, c_1389])).
% 4.05/1.72  tff(c_1408, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1404])).
% 4.05/1.72  tff(c_1411, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1408])).
% 4.05/1.72  tff(c_1415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_1411])).
% 4.05/1.72  tff(c_1417, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1404])).
% 4.05/1.72  tff(c_1416, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1404])).
% 4.05/1.72  tff(c_1424, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1416])).
% 4.05/1.72  tff(c_1427, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1424])).
% 4.05/1.72  tff(c_1431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_1427])).
% 4.05/1.72  tff(c_1433, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1416])).
% 4.05/1.72  tff(c_1432, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1416])).
% 4.05/1.72  tff(c_1044, plain, (![A_118]: (k2_relset_1(k1_relat_1(A_118), k2_relat_1(A_118), A_118)=k2_relat_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_943, c_20])).
% 4.05/1.72  tff(c_1059, plain, (![A_7]: (k2_relset_1(k1_relat_1(k2_funct_1(A_7)), k1_relat_1(A_7), k2_funct_1(A_7))=k2_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1044])).
% 4.05/1.72  tff(c_1446, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1432, c_1059])).
% 4.05/1.72  tff(c_1513, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_44, c_1417, c_1433, c_1446])).
% 4.05/1.72  tff(c_890, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_360])).
% 4.05/1.72  tff(c_923, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_917, c_917, c_890])).
% 4.05/1.72  tff(c_1139, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1137, c_923])).
% 4.05/1.72  tff(c_1657, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1513, c_1139])).
% 4.05/1.72  tff(c_1664, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1657])).
% 4.05/1.72  tff(c_1668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_52, c_44, c_1664])).
% 4.05/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.72  
% 4.05/1.72  Inference rules
% 4.05/1.72  ----------------------
% 4.05/1.72  #Ref     : 0
% 4.05/1.72  #Sup     : 373
% 4.05/1.72  #Fact    : 0
% 4.05/1.72  #Define  : 0
% 4.05/1.72  #Split   : 9
% 4.05/1.72  #Chain   : 0
% 4.05/1.72  #Close   : 0
% 4.05/1.72  
% 4.05/1.72  Ordering : KBO
% 4.05/1.72  
% 4.05/1.72  Simplification rules
% 4.05/1.72  ----------------------
% 4.05/1.72  #Subsume      : 49
% 4.05/1.72  #Demod        : 303
% 4.05/1.72  #Tautology    : 159
% 4.05/1.72  #SimpNegUnit  : 8
% 4.05/1.72  #BackRed      : 32
% 4.05/1.72  
% 4.05/1.72  #Partial instantiations: 0
% 4.05/1.72  #Strategies tried      : 1
% 4.05/1.72  
% 4.05/1.72  Timing (in seconds)
% 4.05/1.72  ----------------------
% 4.05/1.72  Preprocessing        : 0.33
% 4.05/1.72  Parsing              : 0.18
% 4.05/1.72  CNF conversion       : 0.02
% 4.05/1.72  Main loop            : 0.54
% 4.05/1.72  Inferencing          : 0.20
% 4.05/1.72  Reduction            : 0.18
% 4.05/1.72  Demodulation         : 0.13
% 4.05/1.72  BG Simplification    : 0.03
% 4.05/1.72  Subsumption          : 0.08
% 4.05/1.72  Abstraction          : 0.03
% 4.05/1.72  MUC search           : 0.00
% 4.05/1.72  Cooper               : 0.00
% 4.05/1.72  Total                : 0.93
% 4.05/1.72  Index Insertion      : 0.00
% 4.05/1.72  Index Deletion       : 0.00
% 4.05/1.72  Index Matching       : 0.00
% 4.05/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
