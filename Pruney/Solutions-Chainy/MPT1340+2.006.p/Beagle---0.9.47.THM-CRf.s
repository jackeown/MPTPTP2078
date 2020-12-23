%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:30 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :  168 (19628 expanded)
%              Number of leaves         :   45 (6842 expanded)
%              Depth                    :   26
%              Number of atoms          :  433 (57016 expanded)
%              Number of equality atoms :   85 (12841 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_194,negated_conjecture,(
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

tff(f_152,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_160,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_148,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_172,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_70,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_73,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_81,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_73])).

tff(c_66,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_80,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_73])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_112,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_80,c_60])).

tff(c_113,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_113])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_188,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_192,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_188])).

tff(c_58,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_107,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_80,c_58])).

tff(c_205,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_107])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_92,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(u1_struct_0(A_43))
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_98,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_92])).

tff(c_102,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_98])).

tff(c_103,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_102])).

tff(c_214,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_103])).

tff(c_123,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_127,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_112,c_123])).

tff(c_180,plain,(
    ! [B_59,A_60] :
      ( k1_relat_1(B_59) = A_60
      | ~ v1_partfun1(B_59,A_60)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_183,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_180])).

tff(c_186,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_183])).

tff(c_187,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_62])).

tff(c_87,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_86])).

tff(c_215,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_87])).

tff(c_213,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_112])).

tff(c_267,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_270,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_213,c_267])).

tff(c_273,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_215,c_270])).

tff(c_275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_187,c_273])).

tff(c_276,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_280,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_112])).

tff(c_331,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_335,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_331])).

tff(c_281,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_107])).

tff(c_348,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_281])).

tff(c_283,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_87])).

tff(c_355,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_283])).

tff(c_354,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_280])).

tff(c_786,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( r2_funct_2(A_118,B_119,C_120,C_120)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_2(D_121,A_118,B_119)
      | ~ v1_funct_1(D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_2(C_120,A_118,B_119)
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_790,plain,(
    ! [C_120] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_120,C_120)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_120,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_354,c_786])).

tff(c_811,plain,(
    ! [C_122] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_122,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_122,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_790])).

tff(c_816,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_811])).

tff(c_820,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_816])).

tff(c_22,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_353,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_335])).

tff(c_458,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_funct_1(k2_funct_1(C_84))
      | k2_relset_1(A_85,B_86,C_84) != B_86
      | ~ v2_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_461,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_458])).

tff(c_464,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_56,c_353,c_461])).

tff(c_465,plain,(
    ! [C_87,B_88,A_89] :
      ( v1_funct_2(k2_funct_1(C_87),B_88,A_89)
      | k2_relset_1(A_89,B_88,C_87) != B_88
      | ~ v2_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88)))
      | ~ v1_funct_2(C_87,A_89,B_88)
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_468,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_465])).

tff(c_471,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_56,c_353,c_468])).

tff(c_14,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_602,plain,(
    ! [C_97,B_98,A_99] :
      ( m1_subset_1(k2_funct_1(C_97),k1_zfmisc_1(k2_zfmisc_1(B_98,A_99)))
      | k2_relset_1(A_99,B_98,C_97) != B_98
      | ~ v2_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2(C_97,A_99,B_98)
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_24,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_670,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_relat_1(k2_funct_1(C_102))
      | k2_relset_1(A_103,B_104,C_102) != B_104
      | ~ v2_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_2(C_102,A_103,B_104)
      | ~ v1_funct_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_602,c_24])).

tff(c_676,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_670])).

tff(c_680,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_56,c_353,c_676])).

tff(c_28,plain,(
    ! [C_14,A_12,B_13] :
      ( v4_relat_1(C_14,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_692,plain,(
    ! [C_108,B_109,A_110] :
      ( v4_relat_1(k2_funct_1(C_108),B_109)
      | k2_relset_1(A_110,B_109,C_108) != B_109
      | ~ v2_funct_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_2(C_108,A_110,B_109)
      | ~ v1_funct_1(C_108) ) ),
    inference(resolution,[status(thm)],[c_602,c_28])).

tff(c_698,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_692])).

tff(c_702,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_56,c_353,c_698])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( k1_relat_1(B_23) = A_22
      | ~ v1_partfun1(B_23,A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_705,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_702,c_38])).

tff(c_708,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_705])).

tff(c_709,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_16,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_165,plain,(
    ! [A_58] :
      ( k1_relat_1(k2_funct_1(A_58)) = k2_relat_1(A_58)
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [B_23] :
      ( v1_partfun1(B_23,k1_relat_1(B_23))
      | ~ v4_relat_1(B_23,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_444,plain,(
    ! [A_82] :
      ( v1_partfun1(k2_funct_1(A_82),k1_relat_1(k2_funct_1(A_82)))
      | ~ v4_relat_1(k2_funct_1(A_82),k2_relat_1(A_82))
      | ~ v1_relat_1(k2_funct_1(A_82))
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_36])).

tff(c_736,plain,(
    ! [A_117] :
      ( v1_partfun1(k2_funct_1(A_117),k2_relat_1(A_117))
      | ~ v4_relat_1(k2_funct_1(A_117),k2_relat_1(A_117))
      | ~ v1_relat_1(k2_funct_1(A_117))
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117)
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_444])).

tff(c_739,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_702,c_736])).

tff(c_748,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_680,c_739])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_709,c_748])).

tff(c_751,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_429,plain,(
    ! [A_79,B_80] :
      ( v2_funct_1(A_79)
      | k2_relat_1(B_80) != k1_relat_1(A_79)
      | ~ v2_funct_1(k5_relat_1(B_80,A_79))
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_432,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | k1_relat_1(k2_funct_1(A_7)) != k2_relat_1(A_7)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_7)))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_429])).

tff(c_437,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | k1_relat_1(k2_funct_1(A_7)) != k2_relat_1(A_7)
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_432])).

tff(c_397,plain,(
    ! [A_73] :
      ( k5_relat_1(A_73,k2_funct_1(A_73)) = k6_relat_1(k1_relat_1(A_73))
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_406,plain,(
    ! [A_8] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_8))) = k5_relat_1(k2_funct_1(A_8),A_8)
      | ~ v2_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(k2_funct_1(A_8))
      | ~ v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_397])).

tff(c_756,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_406])).

tff(c_772,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_680,c_464,c_756])).

tff(c_795,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_801,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_437,c_795])).

tff(c_808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_680,c_464,c_751,c_801])).

tff(c_810,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_30,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_870,plain,(
    ! [B_124,A_125,C_126] :
      ( k2_relset_1(B_124,A_125,k2_funct_1(C_126)) = k2_relat_1(k2_funct_1(C_126))
      | k2_relset_1(A_125,B_124,C_126) != B_124
      | ~ v2_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_2(C_126,A_125,B_124)
      | ~ v1_funct_1(C_126) ) ),
    inference(resolution,[status(thm)],[c_602,c_30])).

tff(c_876,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_870])).

tff(c_880,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_56,c_353,c_876])).

tff(c_46,plain,(
    ! [C_30,A_28,B_29] :
      ( v1_funct_1(k2_funct_1(C_30))
      | k2_relset_1(A_28,B_29,C_30) != B_29
      | ~ v2_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1189,plain,(
    ! [C_142,B_143,A_144] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_142)))
      | k2_relset_1(B_143,A_144,k2_funct_1(C_142)) != A_144
      | ~ v2_funct_1(k2_funct_1(C_142))
      | ~ v1_funct_2(k2_funct_1(C_142),B_143,A_144)
      | ~ v1_funct_1(k2_funct_1(C_142))
      | k2_relset_1(A_144,B_143,C_142) != B_143
      | ~ v2_funct_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_2(C_142,A_144,B_143)
      | ~ v1_funct_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_602,c_46])).

tff(c_1195,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_1189])).

tff(c_1199,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_56,c_353,c_464,c_471,c_810,c_880,c_1195])).

tff(c_1216,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1199])).

tff(c_1219,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1216])).

tff(c_1223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_1219])).

tff(c_1225,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_1231,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_880])).

tff(c_52,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_tops_2(A_33,B_34,C_35) = k2_funct_1(C_35)
      | ~ v2_funct_1(C_35)
      | k2_relset_1(A_33,B_34,C_35) != B_34
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1461,plain,(
    ! [B_149,A_150,C_151] :
      ( k2_tops_2(B_149,A_150,k2_funct_1(C_151)) = k2_funct_1(k2_funct_1(C_151))
      | ~ v2_funct_1(k2_funct_1(C_151))
      | k2_relset_1(B_149,A_150,k2_funct_1(C_151)) != A_150
      | ~ v1_funct_2(k2_funct_1(C_151),B_149,A_150)
      | ~ v1_funct_1(k2_funct_1(C_151))
      | k2_relset_1(A_150,B_149,C_151) != B_149
      | ~ v2_funct_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149)))
      | ~ v1_funct_2(C_151,A_150,B_149)
      | ~ v1_funct_1(C_151) ) ),
    inference(resolution,[status(thm)],[c_602,c_52])).

tff(c_1467,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_1461])).

tff(c_1471,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_56,c_353,c_464,c_471,c_1231,c_810,c_1467])).

tff(c_515,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_tops_2(A_91,B_92,C_93) = k2_funct_1(C_93)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(A_91,B_92,C_93) != B_92
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(C_93,A_91,B_92)
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_518,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_515])).

tff(c_521,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355,c_353,c_56,c_518])).

tff(c_54,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_164,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_81,c_80,c_80,c_80,c_54])).

tff(c_278,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_276,c_276,c_164])).

tff(c_417,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_348,c_348,c_278])).

tff(c_522,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_417])).

tff(c_1473,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_522])).

tff(c_1480,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1473])).

tff(c_1483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_64,c_56,c_820,c_1480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n011.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 12:44:57 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.68  
% 4.02/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.68  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.02/1.68  
% 4.02/1.68  %Foreground sorts:
% 4.02/1.68  
% 4.02/1.68  
% 4.02/1.68  %Background operators:
% 4.02/1.68  
% 4.02/1.68  
% 4.02/1.68  %Foreground operators:
% 4.02/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.02/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.02/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.02/1.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.02/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.02/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.02/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.02/1.68  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.02/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.02/1.68  tff('#skF_2', type, '#skF_2': $i).
% 4.02/1.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.02/1.68  tff('#skF_3', type, '#skF_3': $i).
% 4.02/1.68  tff('#skF_1', type, '#skF_1': $i).
% 4.02/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.02/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.02/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.02/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.02/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.02/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.02/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.02/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.02/1.68  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.02/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.02/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.02/1.68  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.02/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.02/1.68  
% 4.26/1.70  tff(f_194, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.26/1.70  tff(f_152, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.26/1.70  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.26/1.70  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.26/1.70  tff(f_160, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.26/1.70  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.26/1.70  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.26/1.70  tff(f_110, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.26/1.70  tff(f_132, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.26/1.70  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 4.26/1.70  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.26/1.70  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.26/1.70  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.26/1.70  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.26/1.70  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.26/1.70  tff(f_172, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.26/1.70  tff(c_70, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_73, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.70  tff(c_81, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_73])).
% 4.26/1.70  tff(c_66, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_80, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_73])).
% 4.26/1.70  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_112, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_80, c_60])).
% 4.26/1.70  tff(c_113, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.26/1.70  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_113])).
% 4.26/1.70  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_188, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.26/1.70  tff(c_192, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_188])).
% 4.26/1.70  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_107, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_80, c_58])).
% 4.26/1.70  tff(c_205, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_107])).
% 4.26/1.70  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_92, plain, (![A_43]: (~v1_xboole_0(u1_struct_0(A_43)) | ~l1_struct_0(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.26/1.70  tff(c_98, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_80, c_92])).
% 4.26/1.70  tff(c_102, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_98])).
% 4.26/1.70  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_102])).
% 4.26/1.70  tff(c_214, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_103])).
% 4.26/1.70  tff(c_123, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.26/1.70  tff(c_127, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_112, c_123])).
% 4.26/1.70  tff(c_180, plain, (![B_59, A_60]: (k1_relat_1(B_59)=A_60 | ~v1_partfun1(B_59, A_60) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.26/1.70  tff(c_183, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_127, c_180])).
% 4.26/1.70  tff(c_186, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_183])).
% 4.26/1.70  tff(c_187, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_186])).
% 4.26/1.70  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_86, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_62])).
% 4.26/1.70  tff(c_87, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_86])).
% 4.26/1.70  tff(c_215, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_87])).
% 4.26/1.70  tff(c_213, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_112])).
% 4.26/1.70  tff(c_267, plain, (![C_66, A_67, B_68]: (v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.26/1.70  tff(c_270, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_213, c_267])).
% 4.26/1.70  tff(c_273, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_215, c_270])).
% 4.26/1.70  tff(c_275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_187, c_273])).
% 4.26/1.70  tff(c_276, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_186])).
% 4.26/1.70  tff(c_280, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_112])).
% 4.26/1.70  tff(c_331, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.26/1.70  tff(c_335, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_331])).
% 4.26/1.70  tff(c_281, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_107])).
% 4.26/1.70  tff(c_348, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_281])).
% 4.26/1.70  tff(c_283, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_87])).
% 4.26/1.70  tff(c_355, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_283])).
% 4.26/1.70  tff(c_354, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_280])).
% 4.26/1.70  tff(c_786, plain, (![A_118, B_119, C_120, D_121]: (r2_funct_2(A_118, B_119, C_120, C_120) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_2(D_121, A_118, B_119) | ~v1_funct_1(D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_2(C_120, A_118, B_119) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.26/1.70  tff(c_790, plain, (![C_120]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_120, C_120) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_120, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_120))), inference(resolution, [status(thm)], [c_354, c_786])).
% 4.26/1.70  tff(c_811, plain, (![C_122]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_122, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_122, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_122))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_790])).
% 4.26/1.70  tff(c_816, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_811])).
% 4.26/1.70  tff(c_820, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_816])).
% 4.26/1.70  tff(c_22, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.26/1.70  tff(c_353, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_335])).
% 4.26/1.70  tff(c_458, plain, (![C_84, A_85, B_86]: (v1_funct_1(k2_funct_1(C_84)) | k2_relset_1(A_85, B_86, C_84)!=B_86 | ~v2_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.26/1.70  tff(c_461, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_458])).
% 4.26/1.70  tff(c_464, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_56, c_353, c_461])).
% 4.26/1.70  tff(c_465, plain, (![C_87, B_88, A_89]: (v1_funct_2(k2_funct_1(C_87), B_88, A_89) | k2_relset_1(A_89, B_88, C_87)!=B_88 | ~v2_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))) | ~v1_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.26/1.70  tff(c_468, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_465])).
% 4.26/1.70  tff(c_471, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_56, c_353, c_468])).
% 4.26/1.70  tff(c_14, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.26/1.70  tff(c_602, plain, (![C_97, B_98, A_99]: (m1_subset_1(k2_funct_1(C_97), k1_zfmisc_1(k2_zfmisc_1(B_98, A_99))) | k2_relset_1(A_99, B_98, C_97)!=B_98 | ~v2_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2(C_97, A_99, B_98) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.26/1.70  tff(c_24, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.26/1.70  tff(c_670, plain, (![C_102, A_103, B_104]: (v1_relat_1(k2_funct_1(C_102)) | k2_relset_1(A_103, B_104, C_102)!=B_104 | ~v2_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_2(C_102, A_103, B_104) | ~v1_funct_1(C_102))), inference(resolution, [status(thm)], [c_602, c_24])).
% 4.26/1.70  tff(c_676, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_670])).
% 4.26/1.70  tff(c_680, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_56, c_353, c_676])).
% 4.26/1.70  tff(c_28, plain, (![C_14, A_12, B_13]: (v4_relat_1(C_14, A_12) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.26/1.70  tff(c_692, plain, (![C_108, B_109, A_110]: (v4_relat_1(k2_funct_1(C_108), B_109) | k2_relset_1(A_110, B_109, C_108)!=B_109 | ~v2_funct_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_2(C_108, A_110, B_109) | ~v1_funct_1(C_108))), inference(resolution, [status(thm)], [c_602, c_28])).
% 4.26/1.70  tff(c_698, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_692])).
% 4.26/1.70  tff(c_702, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_56, c_353, c_698])).
% 4.26/1.70  tff(c_38, plain, (![B_23, A_22]: (k1_relat_1(B_23)=A_22 | ~v1_partfun1(B_23, A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.26/1.70  tff(c_705, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_702, c_38])).
% 4.26/1.70  tff(c_708, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_705])).
% 4.26/1.70  tff(c_709, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_708])).
% 4.26/1.70  tff(c_16, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.26/1.70  tff(c_165, plain, (![A_58]: (k1_relat_1(k2_funct_1(A_58))=k2_relat_1(A_58) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.26/1.70  tff(c_36, plain, (![B_23]: (v1_partfun1(B_23, k1_relat_1(B_23)) | ~v4_relat_1(B_23, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.26/1.70  tff(c_444, plain, (![A_82]: (v1_partfun1(k2_funct_1(A_82), k1_relat_1(k2_funct_1(A_82))) | ~v4_relat_1(k2_funct_1(A_82), k2_relat_1(A_82)) | ~v1_relat_1(k2_funct_1(A_82)) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_165, c_36])).
% 4.26/1.70  tff(c_736, plain, (![A_117]: (v1_partfun1(k2_funct_1(A_117), k2_relat_1(A_117)) | ~v4_relat_1(k2_funct_1(A_117), k2_relat_1(A_117)) | ~v1_relat_1(k2_funct_1(A_117)) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_16, c_444])).
% 4.26/1.70  tff(c_739, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_702, c_736])).
% 4.26/1.70  tff(c_748, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_680, c_739])).
% 4.26/1.70  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_709, c_748])).
% 4.26/1.70  tff(c_751, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_708])).
% 4.26/1.70  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.70  tff(c_20, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.70  tff(c_429, plain, (![A_79, B_80]: (v2_funct_1(A_79) | k2_relat_1(B_80)!=k1_relat_1(A_79) | ~v2_funct_1(k5_relat_1(B_80, A_79)) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.26/1.70  tff(c_432, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | k1_relat_1(k2_funct_1(A_7))!=k2_relat_1(A_7) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_7))) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_429])).
% 4.26/1.70  tff(c_437, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | k1_relat_1(k2_funct_1(A_7))!=k2_relat_1(A_7) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_432])).
% 4.26/1.70  tff(c_397, plain, (![A_73]: (k5_relat_1(A_73, k2_funct_1(A_73))=k6_relat_1(k1_relat_1(A_73)) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.70  tff(c_406, plain, (![A_8]: (k6_relat_1(k1_relat_1(k2_funct_1(A_8)))=k5_relat_1(k2_funct_1(A_8), A_8) | ~v2_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(k2_funct_1(A_8)) | ~v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_22, c_397])).
% 4.26/1.70  tff(c_756, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_751, c_406])).
% 4.26/1.70  tff(c_772, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_680, c_464, c_756])).
% 4.26/1.70  tff(c_795, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_772])).
% 4.26/1.70  tff(c_801, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_437, c_795])).
% 4.26/1.70  tff(c_808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_680, c_464, c_751, c_801])).
% 4.26/1.70  tff(c_810, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_772])).
% 4.26/1.70  tff(c_30, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.26/1.70  tff(c_870, plain, (![B_124, A_125, C_126]: (k2_relset_1(B_124, A_125, k2_funct_1(C_126))=k2_relat_1(k2_funct_1(C_126)) | k2_relset_1(A_125, B_124, C_126)!=B_124 | ~v2_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_2(C_126, A_125, B_124) | ~v1_funct_1(C_126))), inference(resolution, [status(thm)], [c_602, c_30])).
% 4.26/1.70  tff(c_876, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_870])).
% 4.26/1.70  tff(c_880, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_56, c_353, c_876])).
% 4.26/1.70  tff(c_46, plain, (![C_30, A_28, B_29]: (v1_funct_1(k2_funct_1(C_30)) | k2_relset_1(A_28, B_29, C_30)!=B_29 | ~v2_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.26/1.70  tff(c_1189, plain, (![C_142, B_143, A_144]: (v1_funct_1(k2_funct_1(k2_funct_1(C_142))) | k2_relset_1(B_143, A_144, k2_funct_1(C_142))!=A_144 | ~v2_funct_1(k2_funct_1(C_142)) | ~v1_funct_2(k2_funct_1(C_142), B_143, A_144) | ~v1_funct_1(k2_funct_1(C_142)) | k2_relset_1(A_144, B_143, C_142)!=B_143 | ~v2_funct_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_2(C_142, A_144, B_143) | ~v1_funct_1(C_142))), inference(resolution, [status(thm)], [c_602, c_46])).
% 4.26/1.70  tff(c_1195, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_1189])).
% 4.26/1.70  tff(c_1199, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_56, c_353, c_464, c_471, c_810, c_880, c_1195])).
% 4.26/1.70  tff(c_1216, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1199])).
% 4.26/1.70  tff(c_1219, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1216])).
% 4.26/1.70  tff(c_1223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_1219])).
% 4.26/1.70  tff(c_1225, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1199])).
% 4.26/1.70  tff(c_1231, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_880])).
% 4.26/1.70  tff(c_52, plain, (![A_33, B_34, C_35]: (k2_tops_2(A_33, B_34, C_35)=k2_funct_1(C_35) | ~v2_funct_1(C_35) | k2_relset_1(A_33, B_34, C_35)!=B_34 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.26/1.70  tff(c_1461, plain, (![B_149, A_150, C_151]: (k2_tops_2(B_149, A_150, k2_funct_1(C_151))=k2_funct_1(k2_funct_1(C_151)) | ~v2_funct_1(k2_funct_1(C_151)) | k2_relset_1(B_149, A_150, k2_funct_1(C_151))!=A_150 | ~v1_funct_2(k2_funct_1(C_151), B_149, A_150) | ~v1_funct_1(k2_funct_1(C_151)) | k2_relset_1(A_150, B_149, C_151)!=B_149 | ~v2_funct_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))) | ~v1_funct_2(C_151, A_150, B_149) | ~v1_funct_1(C_151))), inference(resolution, [status(thm)], [c_602, c_52])).
% 4.26/1.70  tff(c_1467, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_1461])).
% 4.26/1.70  tff(c_1471, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_56, c_353, c_464, c_471, c_1231, c_810, c_1467])).
% 4.26/1.70  tff(c_515, plain, (![A_91, B_92, C_93]: (k2_tops_2(A_91, B_92, C_93)=k2_funct_1(C_93) | ~v2_funct_1(C_93) | k2_relset_1(A_91, B_92, C_93)!=B_92 | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(C_93, A_91, B_92) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.26/1.70  tff(c_518, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_515])).
% 4.26/1.70  tff(c_521, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355, c_353, c_56, c_518])).
% 4.26/1.70  tff(c_54, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.26/1.70  tff(c_164, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_81, c_80, c_80, c_80, c_54])).
% 4.26/1.70  tff(c_278, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_276, c_276, c_164])).
% 4.26/1.70  tff(c_417, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_348, c_348, c_278])).
% 4.26/1.70  tff(c_522, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_417])).
% 4.26/1.70  tff(c_1473, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_522])).
% 4.26/1.70  tff(c_1480, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1473])).
% 4.26/1.70  tff(c_1483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_64, c_56, c_820, c_1480])).
% 4.26/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.70  
% 4.26/1.70  Inference rules
% 4.26/1.70  ----------------------
% 4.26/1.70  #Ref     : 0
% 4.26/1.70  #Sup     : 331
% 4.26/1.70  #Fact    : 0
% 4.26/1.70  #Define  : 0
% 4.26/1.70  #Split   : 9
% 4.26/1.70  #Chain   : 0
% 4.26/1.70  #Close   : 0
% 4.26/1.70  
% 4.26/1.70  Ordering : KBO
% 4.26/1.70  
% 4.26/1.70  Simplification rules
% 4.26/1.70  ----------------------
% 4.26/1.70  #Subsume      : 41
% 4.26/1.70  #Demod        : 476
% 4.26/1.70  #Tautology    : 176
% 4.26/1.70  #SimpNegUnit  : 7
% 4.26/1.70  #BackRed      : 27
% 4.26/1.70  
% 4.26/1.70  #Partial instantiations: 0
% 4.26/1.70  #Strategies tried      : 1
% 4.26/1.70  
% 4.26/1.70  Timing (in seconds)
% 4.26/1.70  ----------------------
% 4.26/1.71  Preprocessing        : 0.35
% 4.26/1.71  Parsing              : 0.19
% 4.26/1.71  CNF conversion       : 0.02
% 4.26/1.71  Main loop            : 0.59
% 4.26/1.71  Inferencing          : 0.20
% 4.26/1.71  Reduction            : 0.22
% 4.26/1.71  Demodulation         : 0.17
% 4.26/1.71  BG Simplification    : 0.03
% 4.26/1.71  Subsumption          : 0.10
% 4.26/1.71  Abstraction          : 0.03
% 4.26/1.71  MUC search           : 0.00
% 4.26/1.71  Cooper               : 0.00
% 4.26/1.71  Total                : 1.00
% 4.26/1.71  Index Insertion      : 0.00
% 4.26/1.71  Index Deletion       : 0.00
% 4.26/1.71  Index Matching       : 0.00
% 4.26/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
