%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:37 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  250 (200444 expanded)
%              Number of leaves         :   49 (69950 expanded)
%              Depth                    :   35
%              Number of atoms          :  680 (576893 expanded)
%              Number of equality atoms :  122 (120642 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_201,negated_conjecture,(
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

tff(f_159,axiom,(
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

tff(f_103,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_139,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

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

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_75,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_73,axiom,(
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

tff(f_179,axiom,(
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

tff(c_72,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_75,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_83,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_75])).

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_82,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_118,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_82,c_62])).

tff(c_133,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_118,c_133])).

tff(c_139,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_136])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_223,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_227,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_223])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_128,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_82,c_60])).

tff(c_228,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_128])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_105,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(u1_struct_0(A_50))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_111,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_105])).

tff(c_115,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_111])).

tff(c_116,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_115])).

tff(c_237,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_116])).

tff(c_140,plain,(
    ! [C_54,A_55,B_56] :
      ( v4_relat_1(C_54,A_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_144,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_118,c_140])).

tff(c_215,plain,(
    ! [B_63,A_64] :
      ( k1_relat_1(B_63) = A_64
      | ~ v1_partfun1(B_63,A_64)
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_218,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_144,c_215])).

tff(c_221,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_218])).

tff(c_222,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_88,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_64])).

tff(c_89,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_88])).

tff(c_238,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_89])).

tff(c_236,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_118])).

tff(c_314,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_partfun1(C_71,A_72)
      | ~ v1_funct_2(C_71,A_72,B_73)
      | ~ v1_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | v1_xboole_0(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_317,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_236,c_314])).

tff(c_320,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_238,c_317])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_222,c_320])).

tff(c_323,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_328,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_118])).

tff(c_379,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_383,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_328,c_379])).

tff(c_327,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_128])).

tff(c_396,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_327])).

tff(c_330,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_89])).

tff(c_403,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_330])).

tff(c_402,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_328])).

tff(c_2498,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( r2_funct_2(A_200,B_201,C_202,C_202)
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_2(D_203,A_200,B_201)
      | ~ v1_funct_1(D_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_2(C_202,A_200,B_201)
      | ~ v1_funct_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2502,plain,(
    ! [C_202] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_202,C_202)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_202,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_202) ) ),
    inference(resolution,[status(thm)],[c_402,c_2498])).

tff(c_2510,plain,(
    ! [C_204] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_204,C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_204,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_2502])).

tff(c_2515,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_2510])).

tff(c_2519,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_2515])).

tff(c_26,plain,(
    ! [A_14] :
      ( k2_funct_1(k2_funct_1(A_14)) = A_14
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_401,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_383])).

tff(c_1797,plain,(
    ! [C_180,A_181,B_182] :
      ( v1_funct_1(k2_funct_1(C_180))
      | k2_relset_1(A_181,B_182,C_180) != B_182
      | ~ v2_funct_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(C_180,A_181,B_182)
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1800,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_1797])).

tff(c_1803,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_58,c_401,c_1800])).

tff(c_1902,plain,(
    ! [C_184,B_185,A_186] :
      ( v1_funct_2(k2_funct_1(C_184),B_185,A_186)
      | k2_relset_1(A_186,B_185,C_184) != B_185
      | ~ v2_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185)))
      | ~ v1_funct_2(C_184,A_186,B_185)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1905,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_1902])).

tff(c_1908,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_58,c_401,c_1905])).

tff(c_178,plain,(
    ! [A_62] :
      ( k4_relat_1(A_62) = k2_funct_1(A_62)
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_184,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_178])).

tff(c_188,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_184])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_195,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_6])).

tff(c_201,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_195])).

tff(c_2262,plain,(
    ! [C_197,B_198,A_199] :
      ( m1_subset_1(k2_funct_1(C_197),k1_zfmisc_1(k2_zfmisc_1(B_198,A_199)))
      | k2_relset_1(A_199,B_198,C_197) != B_198
      | ~ v2_funct_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_2(C_197,A_199,B_198)
      | ~ v1_funct_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2983,plain,(
    ! [B_222,A_223,C_224] :
      ( k2_relset_1(B_222,A_223,k2_funct_1(C_224)) = k2_relat_1(k2_funct_1(C_224))
      | k2_relset_1(A_223,B_222,C_224) != B_222
      | ~ v2_funct_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222)))
      | ~ v1_funct_2(C_224,A_223,B_222)
      | ~ v1_funct_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_2262,c_32])).

tff(c_2989,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_2983])).

tff(c_2993,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_58,c_401,c_201,c_2989])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_192,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_8])).

tff(c_199,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_192])).

tff(c_38,plain,(
    ! [B_26] :
      ( v1_partfun1(B_26,k1_relat_1(B_26))
      | ~ v4_relat_1(B_26,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_206,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_38])).

tff(c_209,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_206])).

tff(c_459,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_462,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_459])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_462])).

tff(c_468,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_20,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_13] :
      ( k5_relat_1(k2_funct_1(A_13),A_13) = k6_relat_1(k2_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1770,plain,(
    ! [B_176,A_177] :
      ( v2_funct_1(B_176)
      | k2_relat_1(B_176) != k1_relat_1(A_177)
      | ~ v2_funct_1(k5_relat_1(B_176,A_177))
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176)
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1776,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k2_relat_1(k2_funct_1(A_13)) != k1_relat_1(A_13)
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_13)))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1770])).

tff(c_1780,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k2_relat_1(k2_funct_1(A_13)) != k1_relat_1(A_13)
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1776])).

tff(c_384,plain,(
    ! [A_77] :
      ( k5_relat_1(k2_funct_1(A_77),A_77) = k6_relat_1(k2_relat_1(A_77))
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1804,plain,(
    ! [A_183] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(A_183))) = k5_relat_1(A_183,k2_funct_1(A_183))
      | ~ v2_funct_1(k2_funct_1(A_183))
      | ~ v1_funct_1(k2_funct_1(A_183))
      | ~ v1_relat_1(k2_funct_1(A_183))
      | ~ v2_funct_1(A_183)
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_384])).

tff(c_1836,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_1804])).

tff(c_1849,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_468,c_1803,c_1836])).

tff(c_1850,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1849])).

tff(c_1853,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1780,c_1850])).

tff(c_1860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_468,c_1803,c_201,c_1853])).

tff(c_1862,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1849])).

tff(c_44,plain,(
    ! [C_33,B_32,A_31] :
      ( m1_subset_1(k2_funct_1(C_33),k1_zfmisc_1(k2_zfmisc_1(B_32,A_31)))
      | k2_relset_1(A_31,B_32,C_33) != B_32
      | ~ v2_funct_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_10,plain,(
    ! [A_7] :
      ( k4_relat_1(A_7) = k2_funct_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1865,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1862,c_10])).

tff(c_1868,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_1803,c_1865])).

tff(c_1432,plain,(
    ! [C_156,A_157,B_158] :
      ( v1_funct_1(k2_funct_1(C_156))
      | k2_relset_1(A_157,B_158,C_156) != B_158
      | ~ v2_funct_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_2(C_156,A_157,B_158)
      | ~ v1_funct_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1435,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_1432])).

tff(c_1438,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_58,c_401,c_1435])).

tff(c_24,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1405,plain,(
    ! [A_152,B_153] :
      ( v2_funct_1(A_152)
      | k2_relat_1(B_153) != k1_relat_1(A_152)
      | ~ v2_funct_1(k5_relat_1(B_153,A_152))
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1408,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k1_relat_1(k2_funct_1(A_13)) != k2_relat_1(A_13)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_13)))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13)
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1405])).

tff(c_1413,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k1_relat_1(k2_funct_1(A_13)) != k2_relat_1(A_13)
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1408])).

tff(c_447,plain,(
    ! [A_79] :
      ( k5_relat_1(A_79,k2_funct_1(A_79)) = k6_relat_1(k1_relat_1(A_79))
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1446,plain,(
    ! [A_162] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_162))) = k5_relat_1(k2_funct_1(A_162),A_162)
      | ~ v2_funct_1(k2_funct_1(A_162))
      | ~ v1_funct_1(k2_funct_1(A_162))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_447])).

tff(c_1478,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_1446])).

tff(c_1491,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_468,c_1438,c_1478])).

tff(c_1492,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1491])).

tff(c_1495,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1413,c_1492])).

tff(c_1502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_468,c_1438,c_199,c_1495])).

tff(c_1504,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1491])).

tff(c_1507,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1504,c_10])).

tff(c_1510,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_1438,c_1507])).

tff(c_174,plain,(
    ! [B_61] :
      ( v1_partfun1(B_61,k1_relat_1(B_61))
      | ~ v4_relat_1(B_61,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1365,plain,(
    ! [A_148] :
      ( v1_partfun1(k4_relat_1(A_148),k1_relat_1(k4_relat_1(A_148)))
      | ~ v4_relat_1(k4_relat_1(A_148),k2_relat_1(A_148))
      | ~ v1_relat_1(k4_relat_1(A_148))
      | ~ v1_relat_1(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_174])).

tff(c_1379,plain,(
    ! [A_149] :
      ( v1_partfun1(k4_relat_1(A_149),k2_relat_1(A_149))
      | ~ v4_relat_1(k4_relat_1(A_149),k2_relat_1(A_149))
      | ~ v1_relat_1(k4_relat_1(A_149))
      | ~ v1_relat_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1365])).

tff(c_1382,plain,
    ( v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_1379])).

tff(c_1390,plain,
    ( v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_468,c_201,c_1382])).

tff(c_1393,plain,(
    ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1390])).

tff(c_1511,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1393])).

tff(c_1543,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1511])).

tff(c_1549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_139,c_1543])).

tff(c_1551,plain,(
    v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1390])).

tff(c_326,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_144])).

tff(c_1575,plain,(
    ! [C_167,A_168,B_169] :
      ( v1_funct_1(k2_funct_1(C_167))
      | k2_relset_1(A_168,B_169,C_167) != B_169
      | ~ v2_funct_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_2(C_167,A_168,B_169)
      | ~ v1_funct_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1578,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_1575])).

tff(c_1581,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_58,c_401,c_1578])).

tff(c_1564,plain,(
    ! [B_165,A_166] :
      ( v2_funct_1(B_165)
      | k2_relat_1(B_165) != k1_relat_1(A_166)
      | ~ v2_funct_1(k5_relat_1(B_165,A_166))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1570,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k2_relat_1(k2_funct_1(A_13)) != k1_relat_1(A_13)
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_13)))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1564])).

tff(c_1574,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k2_relat_1(k2_funct_1(A_13)) != k1_relat_1(A_13)
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1570])).

tff(c_1598,plain,(
    ! [A_172] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_172))) = k5_relat_1(k2_funct_1(A_172),A_172)
      | ~ v2_funct_1(k2_funct_1(A_172))
      | ~ v1_funct_1(k2_funct_1(A_172))
      | ~ v1_relat_1(k2_funct_1(A_172))
      | ~ v2_funct_1(A_172)
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_447])).

tff(c_1630,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_1598])).

tff(c_1643,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_468,c_1581,c_1630])).

tff(c_1644,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1643])).

tff(c_1654,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1574,c_1644])).

tff(c_1661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_468,c_1581,c_201,c_1654])).

tff(c_1663,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1643])).

tff(c_1666,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1663,c_10])).

tff(c_1669,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_1581,c_1666])).

tff(c_1550,plain,
    ( ~ v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1390])).

tff(c_1563,plain,(
    ~ v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1550])).

tff(c_1670,plain,(
    ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1563])).

tff(c_1734,plain,
    ( ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1670])).

tff(c_1737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_326,c_1734])).

tff(c_1738,plain,(
    v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1550])).

tff(c_1739,plain,(
    v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1550])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( k1_relat_1(B_26) = A_25
      | ~ v1_partfun1(B_26,A_25)
      | ~ v4_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1742,plain,
    ( k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1739,c_40])).

tff(c_1745,plain,(
    k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_1738,c_1742])).

tff(c_1869,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_1745])).

tff(c_1872,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_1551])).

tff(c_1552,plain,(
    ! [A_163,B_164] :
      ( v2_funct_1(A_163)
      | k2_relat_1(B_164) != k1_relat_1(A_163)
      | ~ v2_funct_1(k5_relat_1(B_164,A_163))
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1555,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k1_relat_1(k2_funct_1(A_13)) != k2_relat_1(A_13)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_13)))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13)
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1552])).

tff(c_1781,plain,(
    ! [A_178] :
      ( v2_funct_1(k2_funct_1(A_178))
      | k1_relat_1(k2_funct_1(A_178)) != k2_relat_1(A_178)
      | ~ v1_funct_1(k2_funct_1(A_178))
      | ~ v1_relat_1(k2_funct_1(A_178))
      | ~ v2_funct_1(A_178)
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1555])).

tff(c_2242,plain,(
    ! [A_196] :
      ( k4_relat_1(k2_funct_1(A_196)) = k2_funct_1(k2_funct_1(A_196))
      | k1_relat_1(k2_funct_1(A_196)) != k2_relat_1(A_196)
      | ~ v1_funct_1(k2_funct_1(A_196))
      | ~ v1_relat_1(k2_funct_1(A_196))
      | ~ v2_funct_1(A_196)
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(resolution,[status(thm)],[c_1781,c_10])).

tff(c_2245,plain,
    ( k4_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) != k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1872,c_2242])).

tff(c_2257,plain,
    ( k4_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_1803,c_1862,c_201,c_1869,c_2245])).

tff(c_2300,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2257])).

tff(c_2303,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2300])).

tff(c_2309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_66,c_2303])).

tff(c_2311,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2257])).

tff(c_1888,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_6])).

tff(c_1900,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_199,c_1888])).

tff(c_2310,plain,(
    k4_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2257])).

tff(c_2340,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k4_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2310])).

tff(c_2354,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_188,c_2340])).

tff(c_1824,plain,(
    ! [A_183] :
      ( v2_funct_1(k5_relat_1(A_183,k2_funct_1(A_183)))
      | ~ v2_funct_1(k2_funct_1(A_183))
      | ~ v1_funct_1(k2_funct_1(A_183))
      | ~ v1_relat_1(k2_funct_1(A_183))
      | ~ v2_funct_1(A_183)
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1804,c_20])).

tff(c_2389,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2354,c_1824])).

tff(c_2434,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_2311,c_468,c_2354,c_1803,c_2354,c_1862,c_2354,c_2389])).

tff(c_2520,plain,(
    ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2434])).

tff(c_2523,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1780,c_2520])).

tff(c_2533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_1803,c_1862,c_1872,c_2311,c_199,c_1900,c_2523])).

tff(c_2535,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2434])).

tff(c_3543,plain,(
    ! [A_241,B_242,A_243] :
      ( m1_subset_1(A_241,k1_zfmisc_1(k2_zfmisc_1(B_242,A_243)))
      | k2_relset_1(A_243,B_242,k2_funct_1(A_241)) != B_242
      | ~ v2_funct_1(k2_funct_1(A_241))
      | ~ m1_subset_1(k2_funct_1(A_241),k1_zfmisc_1(k2_zfmisc_1(A_243,B_242)))
      | ~ v1_funct_2(k2_funct_1(A_241),A_243,B_242)
      | ~ v1_funct_1(k2_funct_1(A_241))
      | ~ v2_funct_1(A_241)
      | ~ v1_funct_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2262])).

tff(c_3546,plain,(
    ! [B_242,A_243] :
      ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(B_242,A_243)))
      | k2_relset_1(A_243,B_242,k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) != B_242
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
      | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(A_243,B_242)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),A_243,B_242)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2354,c_3543])).

tff(c_3556,plain,(
    ! [B_244,A_245] :
      ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(B_244,A_245)))
      | k2_relset_1(A_245,B_244,k2_funct_1('#skF_3')) != B_244
      | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_2(k2_funct_1('#skF_3'),A_245,B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_2311,c_2535,c_1803,c_2354,c_2354,c_1862,c_2354,c_2354,c_3546])).

tff(c_2506,plain,(
    ! [C_202] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_202,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_202,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_2502])).

tff(c_3583,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3556,c_2506])).

tff(c_3639,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_2993,c_2311,c_3583])).

tff(c_3680,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_3639])).

tff(c_3683,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_3680])).

tff(c_3687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_402,c_58,c_401,c_3683])).

tff(c_3689,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_3639])).

tff(c_54,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_tops_2(A_36,B_37,C_38) = k2_funct_1(C_38)
      | ~ v2_funct_1(C_38)
      | k2_relset_1(A_36,B_37,C_38) != B_37
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_3722,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3689,c_54])).

tff(c_3780,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1803,c_1908,c_2993,c_1862,c_3722])).

tff(c_1988,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_tops_2(A_187,B_188,C_189) = k2_funct_1(C_189)
      | ~ v2_funct_1(C_189)
      | k2_relset_1(A_187,B_188,C_189) != B_188
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(C_189,A_187,B_188)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1991,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_1988])).

tff(c_1994,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403,c_401,c_58,c_1991])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_173,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_83,c_82,c_82,c_82,c_56])).

tff(c_325,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_323,c_323,c_173])).

tff(c_469,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_396,c_396,c_325])).

tff(c_1995,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_469])).

tff(c_3843,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3780,c_1995])).

tff(c_3850,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3843])).

tff(c_3853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_58,c_2519,c_3850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.06  
% 5.60/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.06  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.60/2.06  
% 5.60/2.06  %Foreground sorts:
% 5.60/2.06  
% 5.60/2.06  
% 5.60/2.06  %Background operators:
% 5.60/2.06  
% 5.60/2.06  
% 5.60/2.06  %Foreground operators:
% 5.60/2.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.60/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.60/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.60/2.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.60/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.60/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.60/2.06  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.60/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.60/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.60/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.60/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.60/2.06  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.60/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.60/2.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.60/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.60/2.06  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.60/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.60/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.60/2.06  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.60/2.06  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.60/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.06  
% 5.80/2.09  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.80/2.09  tff(f_201, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 5.80/2.09  tff(f_159, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.80/2.09  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.80/2.09  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.80/2.09  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.80/2.09  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.80/2.09  tff(f_125, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 5.80/2.09  tff(f_117, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.80/2.09  tff(f_139, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 5.80/2.09  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.80/2.09  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.80/2.09  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 5.80/2.09  tff(f_40, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 5.80/2.09  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.80/2.09  tff(f_75, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 5.80/2.09  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.80/2.09  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 5.80/2.09  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.80/2.09  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.80/2.09  tff(c_72, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_75, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.80/2.09  tff(c_83, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_75])).
% 5.80/2.09  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_82, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_75])).
% 5.80/2.09  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_118, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_82, c_62])).
% 5.80/2.09  tff(c_133, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.80/2.09  tff(c_136, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_118, c_133])).
% 5.80/2.09  tff(c_139, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_136])).
% 5.80/2.09  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_223, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.80/2.09  tff(c_227, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_118, c_223])).
% 5.80/2.09  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_128, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_82, c_60])).
% 5.80/2.09  tff(c_228, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_128])).
% 5.80/2.09  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_105, plain, (![A_50]: (~v1_xboole_0(u1_struct_0(A_50)) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.80/2.09  tff(c_111, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_82, c_105])).
% 5.80/2.09  tff(c_115, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_111])).
% 5.80/2.09  tff(c_116, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_115])).
% 5.80/2.09  tff(c_237, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_116])).
% 5.80/2.09  tff(c_140, plain, (![C_54, A_55, B_56]: (v4_relat_1(C_54, A_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.80/2.09  tff(c_144, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_118, c_140])).
% 5.80/2.09  tff(c_215, plain, (![B_63, A_64]: (k1_relat_1(B_63)=A_64 | ~v1_partfun1(B_63, A_64) | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.80/2.09  tff(c_218, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_144, c_215])).
% 5.80/2.09  tff(c_221, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_218])).
% 5.80/2.09  tff(c_222, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_221])).
% 5.80/2.09  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_88, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_64])).
% 5.80/2.09  tff(c_89, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_88])).
% 5.80/2.09  tff(c_238, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_89])).
% 5.80/2.09  tff(c_236, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_118])).
% 5.80/2.09  tff(c_314, plain, (![C_71, A_72, B_73]: (v1_partfun1(C_71, A_72) | ~v1_funct_2(C_71, A_72, B_73) | ~v1_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | v1_xboole_0(B_73))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.80/2.09  tff(c_317, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_236, c_314])).
% 5.80/2.09  tff(c_320, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_238, c_317])).
% 5.80/2.09  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_222, c_320])).
% 5.80/2.09  tff(c_323, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_221])).
% 5.80/2.09  tff(c_328, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_118])).
% 5.80/2.09  tff(c_379, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.80/2.09  tff(c_383, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_328, c_379])).
% 5.80/2.09  tff(c_327, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_128])).
% 5.80/2.09  tff(c_396, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_327])).
% 5.80/2.09  tff(c_330, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_89])).
% 5.80/2.09  tff(c_403, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_330])).
% 5.80/2.09  tff(c_402, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_328])).
% 5.80/2.09  tff(c_2498, plain, (![A_200, B_201, C_202, D_203]: (r2_funct_2(A_200, B_201, C_202, C_202) | ~m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_2(D_203, A_200, B_201) | ~v1_funct_1(D_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_2(C_202, A_200, B_201) | ~v1_funct_1(C_202))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.80/2.09  tff(c_2502, plain, (![C_202]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_202, C_202) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_202, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_202))), inference(resolution, [status(thm)], [c_402, c_2498])).
% 5.80/2.09  tff(c_2510, plain, (![C_204]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_204, C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_204, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_204))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_2502])).
% 5.80/2.09  tff(c_2515, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_2510])).
% 5.80/2.09  tff(c_2519, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_2515])).
% 5.80/2.09  tff(c_26, plain, (![A_14]: (k2_funct_1(k2_funct_1(A_14))=A_14 | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.80/2.09  tff(c_401, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_383])).
% 5.80/2.09  tff(c_1797, plain, (![C_180, A_181, B_182]: (v1_funct_1(k2_funct_1(C_180)) | k2_relset_1(A_181, B_182, C_180)!=B_182 | ~v2_funct_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_2(C_180, A_181, B_182) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.80/2.09  tff(c_1800, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_1797])).
% 5.80/2.09  tff(c_1803, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_58, c_401, c_1800])).
% 5.80/2.09  tff(c_1902, plain, (![C_184, B_185, A_186]: (v1_funct_2(k2_funct_1(C_184), B_185, A_186) | k2_relset_1(A_186, B_185, C_184)!=B_185 | ~v2_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))) | ~v1_funct_2(C_184, A_186, B_185) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.80/2.09  tff(c_1905, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_1902])).
% 5.80/2.09  tff(c_1908, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_58, c_401, c_1905])).
% 5.80/2.09  tff(c_178, plain, (![A_62]: (k4_relat_1(A_62)=k2_funct_1(A_62) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.80/2.09  tff(c_184, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_178])).
% 5.80/2.09  tff(c_188, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_184])).
% 5.80/2.09  tff(c_6, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.80/2.09  tff(c_195, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_188, c_6])).
% 5.80/2.09  tff(c_201, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_195])).
% 5.80/2.09  tff(c_2262, plain, (![C_197, B_198, A_199]: (m1_subset_1(k2_funct_1(C_197), k1_zfmisc_1(k2_zfmisc_1(B_198, A_199))) | k2_relset_1(A_199, B_198, C_197)!=B_198 | ~v2_funct_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_2(C_197, A_199, B_198) | ~v1_funct_1(C_197))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.80/2.09  tff(c_32, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.80/2.09  tff(c_2983, plain, (![B_222, A_223, C_224]: (k2_relset_1(B_222, A_223, k2_funct_1(C_224))=k2_relat_1(k2_funct_1(C_224)) | k2_relset_1(A_223, B_222, C_224)!=B_222 | ~v2_funct_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))) | ~v1_funct_2(C_224, A_223, B_222) | ~v1_funct_1(C_224))), inference(resolution, [status(thm)], [c_2262, c_32])).
% 5.80/2.09  tff(c_2989, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_2983])).
% 5.80/2.09  tff(c_2993, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_58, c_401, c_201, c_2989])).
% 5.80/2.09  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.80/2.09  tff(c_8, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.80/2.09  tff(c_192, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_188, c_8])).
% 5.80/2.09  tff(c_199, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_192])).
% 5.80/2.09  tff(c_38, plain, (![B_26]: (v1_partfun1(B_26, k1_relat_1(B_26)) | ~v4_relat_1(B_26, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.80/2.09  tff(c_206, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_38])).
% 5.80/2.09  tff(c_209, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_206])).
% 5.80/2.09  tff(c_459, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_209])).
% 5.80/2.09  tff(c_462, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_459])).
% 5.80/2.09  tff(c_466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_462])).
% 5.80/2.09  tff(c_468, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_209])).
% 5.80/2.09  tff(c_20, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.80/2.09  tff(c_22, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_relat_1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.09  tff(c_1770, plain, (![B_176, A_177]: (v2_funct_1(B_176) | k2_relat_1(B_176)!=k1_relat_1(A_177) | ~v2_funct_1(k5_relat_1(B_176, A_177)) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.80/2.09  tff(c_1776, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_13))) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1770])).
% 5.80/2.09  tff(c_1780, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1776])).
% 5.80/2.09  tff(c_384, plain, (![A_77]: (k5_relat_1(k2_funct_1(A_77), A_77)=k6_relat_1(k2_relat_1(A_77)) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.09  tff(c_1804, plain, (![A_183]: (k6_relat_1(k2_relat_1(k2_funct_1(A_183)))=k5_relat_1(A_183, k2_funct_1(A_183)) | ~v2_funct_1(k2_funct_1(A_183)) | ~v1_funct_1(k2_funct_1(A_183)) | ~v1_relat_1(k2_funct_1(A_183)) | ~v2_funct_1(A_183) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_26, c_384])).
% 5.80/2.09  tff(c_1836, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_201, c_1804])).
% 5.80/2.09  tff(c_1849, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_468, c_1803, c_1836])).
% 5.80/2.09  tff(c_1850, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1849])).
% 5.80/2.09  tff(c_1853, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1780, c_1850])).
% 5.80/2.09  tff(c_1860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_468, c_1803, c_201, c_1853])).
% 5.80/2.09  tff(c_1862, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1849])).
% 5.80/2.09  tff(c_44, plain, (![C_33, B_32, A_31]: (m1_subset_1(k2_funct_1(C_33), k1_zfmisc_1(k2_zfmisc_1(B_32, A_31))) | k2_relset_1(A_31, B_32, C_33)!=B_32 | ~v2_funct_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.80/2.09  tff(c_10, plain, (![A_7]: (k4_relat_1(A_7)=k2_funct_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.80/2.09  tff(c_1865, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1862, c_10])).
% 5.80/2.09  tff(c_1868, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_1803, c_1865])).
% 5.80/2.09  tff(c_1432, plain, (![C_156, A_157, B_158]: (v1_funct_1(k2_funct_1(C_156)) | k2_relset_1(A_157, B_158, C_156)!=B_158 | ~v2_funct_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_2(C_156, A_157, B_158) | ~v1_funct_1(C_156))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.80/2.09  tff(c_1435, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_1432])).
% 5.80/2.09  tff(c_1438, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_58, c_401, c_1435])).
% 5.80/2.09  tff(c_24, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.09  tff(c_1405, plain, (![A_152, B_153]: (v2_funct_1(A_152) | k2_relat_1(B_153)!=k1_relat_1(A_152) | ~v2_funct_1(k5_relat_1(B_153, A_152)) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.80/2.09  tff(c_1408, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k1_relat_1(k2_funct_1(A_13))!=k2_relat_1(A_13) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_13))) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1405])).
% 5.80/2.09  tff(c_1413, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k1_relat_1(k2_funct_1(A_13))!=k2_relat_1(A_13) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1408])).
% 5.80/2.09  tff(c_447, plain, (![A_79]: (k5_relat_1(A_79, k2_funct_1(A_79))=k6_relat_1(k1_relat_1(A_79)) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.09  tff(c_1446, plain, (![A_162]: (k6_relat_1(k1_relat_1(k2_funct_1(A_162)))=k5_relat_1(k2_funct_1(A_162), A_162) | ~v2_funct_1(k2_funct_1(A_162)) | ~v1_funct_1(k2_funct_1(A_162)) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_26, c_447])).
% 5.80/2.09  tff(c_1478, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_199, c_1446])).
% 5.80/2.09  tff(c_1491, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_468, c_1438, c_1478])).
% 5.80/2.09  tff(c_1492, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1491])).
% 5.80/2.09  tff(c_1495, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1413, c_1492])).
% 5.80/2.09  tff(c_1502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_468, c_1438, c_199, c_1495])).
% 5.80/2.09  tff(c_1504, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1491])).
% 5.80/2.09  tff(c_1507, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1504, c_10])).
% 5.80/2.09  tff(c_1510, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_1438, c_1507])).
% 5.80/2.09  tff(c_174, plain, (![B_61]: (v1_partfun1(B_61, k1_relat_1(B_61)) | ~v4_relat_1(B_61, k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.80/2.09  tff(c_1365, plain, (![A_148]: (v1_partfun1(k4_relat_1(A_148), k1_relat_1(k4_relat_1(A_148))) | ~v4_relat_1(k4_relat_1(A_148), k2_relat_1(A_148)) | ~v1_relat_1(k4_relat_1(A_148)) | ~v1_relat_1(A_148))), inference(superposition, [status(thm), theory('equality')], [c_8, c_174])).
% 5.80/2.09  tff(c_1379, plain, (![A_149]: (v1_partfun1(k4_relat_1(A_149), k2_relat_1(A_149)) | ~v4_relat_1(k4_relat_1(A_149), k2_relat_1(A_149)) | ~v1_relat_1(k4_relat_1(A_149)) | ~v1_relat_1(A_149) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1365])).
% 5.80/2.09  tff(c_1382, plain, (v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_1379])).
% 5.80/2.09  tff(c_1390, plain, (v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_468, c_201, c_1382])).
% 5.80/2.09  tff(c_1393, plain, (~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1390])).
% 5.80/2.09  tff(c_1511, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1393])).
% 5.80/2.09  tff(c_1543, plain, (~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1511])).
% 5.80/2.09  tff(c_1549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_139, c_1543])).
% 5.80/2.09  tff(c_1551, plain, (v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1390])).
% 5.80/2.09  tff(c_326, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_144])).
% 5.80/2.09  tff(c_1575, plain, (![C_167, A_168, B_169]: (v1_funct_1(k2_funct_1(C_167)) | k2_relset_1(A_168, B_169, C_167)!=B_169 | ~v2_funct_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_2(C_167, A_168, B_169) | ~v1_funct_1(C_167))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.80/2.09  tff(c_1578, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_1575])).
% 5.80/2.09  tff(c_1581, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_58, c_401, c_1578])).
% 5.80/2.09  tff(c_1564, plain, (![B_165, A_166]: (v2_funct_1(B_165) | k2_relat_1(B_165)!=k1_relat_1(A_166) | ~v2_funct_1(k5_relat_1(B_165, A_166)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.80/2.09  tff(c_1570, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_13))) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1564])).
% 5.80/2.09  tff(c_1574, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1570])).
% 5.80/2.09  tff(c_1598, plain, (![A_172]: (k6_relat_1(k1_relat_1(k2_funct_1(A_172)))=k5_relat_1(k2_funct_1(A_172), A_172) | ~v2_funct_1(k2_funct_1(A_172)) | ~v1_funct_1(k2_funct_1(A_172)) | ~v1_relat_1(k2_funct_1(A_172)) | ~v2_funct_1(A_172) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(superposition, [status(thm), theory('equality')], [c_26, c_447])).
% 5.80/2.09  tff(c_1630, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_199, c_1598])).
% 5.80/2.09  tff(c_1643, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_468, c_1581, c_1630])).
% 5.80/2.09  tff(c_1644, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1643])).
% 5.80/2.09  tff(c_1654, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1574, c_1644])).
% 5.80/2.09  tff(c_1661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_468, c_1581, c_201, c_1654])).
% 5.80/2.09  tff(c_1663, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1643])).
% 5.80/2.09  tff(c_1666, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1663, c_10])).
% 5.80/2.09  tff(c_1669, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_1581, c_1666])).
% 5.80/2.09  tff(c_1550, plain, (~v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1390])).
% 5.80/2.09  tff(c_1563, plain, (~v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1550])).
% 5.80/2.09  tff(c_1670, plain, (~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1563])).
% 5.80/2.09  tff(c_1734, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1670])).
% 5.80/2.09  tff(c_1737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_326, c_1734])).
% 5.80/2.09  tff(c_1738, plain, (v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1550])).
% 5.80/2.09  tff(c_1739, plain, (v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1550])).
% 5.80/2.09  tff(c_40, plain, (![B_26, A_25]: (k1_relat_1(B_26)=A_25 | ~v1_partfun1(B_26, A_25) | ~v4_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.80/2.09  tff(c_1742, plain, (k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3') | ~v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1739, c_40])).
% 5.80/2.09  tff(c_1745, plain, (k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_1738, c_1742])).
% 5.80/2.09  tff(c_1869, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_1745])).
% 5.80/2.09  tff(c_1872, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_1551])).
% 5.80/2.09  tff(c_1552, plain, (![A_163, B_164]: (v2_funct_1(A_163) | k2_relat_1(B_164)!=k1_relat_1(A_163) | ~v2_funct_1(k5_relat_1(B_164, A_163)) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.80/2.09  tff(c_1555, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k1_relat_1(k2_funct_1(A_13))!=k2_relat_1(A_13) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_13))) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1552])).
% 5.80/2.09  tff(c_1781, plain, (![A_178]: (v2_funct_1(k2_funct_1(A_178)) | k1_relat_1(k2_funct_1(A_178))!=k2_relat_1(A_178) | ~v1_funct_1(k2_funct_1(A_178)) | ~v1_relat_1(k2_funct_1(A_178)) | ~v2_funct_1(A_178) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1555])).
% 5.80/2.09  tff(c_2242, plain, (![A_196]: (k4_relat_1(k2_funct_1(A_196))=k2_funct_1(k2_funct_1(A_196)) | k1_relat_1(k2_funct_1(A_196))!=k2_relat_1(A_196) | ~v1_funct_1(k2_funct_1(A_196)) | ~v1_relat_1(k2_funct_1(A_196)) | ~v2_funct_1(A_196) | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(resolution, [status(thm)], [c_1781, c_10])).
% 5.80/2.09  tff(c_2245, plain, (k4_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))!=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1872, c_2242])).
% 5.80/2.09  tff(c_2257, plain, (k4_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_1803, c_1862, c_201, c_1869, c_2245])).
% 5.80/2.09  tff(c_2300, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2257])).
% 5.80/2.09  tff(c_2303, plain, (~v1_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2300])).
% 5.80/2.09  tff(c_2309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_66, c_2303])).
% 5.80/2.09  tff(c_2311, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2257])).
% 5.80/2.09  tff(c_1888, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1868, c_6])).
% 5.80/2.09  tff(c_1900, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_199, c_1888])).
% 5.80/2.09  tff(c_2310, plain, (k4_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2257])).
% 5.80/2.09  tff(c_2340, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k4_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2310])).
% 5.80/2.09  tff(c_2354, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_188, c_2340])).
% 5.80/2.09  tff(c_1824, plain, (![A_183]: (v2_funct_1(k5_relat_1(A_183, k2_funct_1(A_183))) | ~v2_funct_1(k2_funct_1(A_183)) | ~v1_funct_1(k2_funct_1(A_183)) | ~v1_relat_1(k2_funct_1(A_183)) | ~v2_funct_1(A_183) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_1804, c_20])).
% 5.80/2.09  tff(c_2389, plain, (v2_funct_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2354, c_1824])).
% 5.80/2.09  tff(c_2434, plain, (v2_funct_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_2311, c_468, c_2354, c_1803, c_2354, c_1862, c_2354, c_2389])).
% 5.80/2.09  tff(c_2520, plain, (~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2434])).
% 5.80/2.09  tff(c_2523, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1780, c_2520])).
% 5.80/2.09  tff(c_2533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_468, c_1803, c_1862, c_1872, c_2311, c_199, c_1900, c_2523])).
% 5.80/2.09  tff(c_2535, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2434])).
% 5.80/2.09  tff(c_3543, plain, (![A_241, B_242, A_243]: (m1_subset_1(A_241, k1_zfmisc_1(k2_zfmisc_1(B_242, A_243))) | k2_relset_1(A_243, B_242, k2_funct_1(A_241))!=B_242 | ~v2_funct_1(k2_funct_1(A_241)) | ~m1_subset_1(k2_funct_1(A_241), k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))) | ~v1_funct_2(k2_funct_1(A_241), A_243, B_242) | ~v1_funct_1(k2_funct_1(A_241)) | ~v2_funct_1(A_241) | ~v1_funct_1(A_241) | ~v1_relat_1(A_241))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2262])).
% 5.80/2.09  tff(c_3546, plain, (![B_242, A_243]: (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(B_242, A_243))) | k2_relset_1(A_243, B_242, k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))!=B_242 | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))) | ~v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), A_243, B_242) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_2354, c_3543])).
% 5.80/2.09  tff(c_3556, plain, (![B_244, A_245]: (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(B_244, A_245))) | k2_relset_1(A_245, B_244, k2_funct_1('#skF_3'))!=B_244 | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_2(k2_funct_1('#skF_3'), A_245, B_244))), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_2311, c_2535, c_1803, c_2354, c_2354, c_1862, c_2354, c_2354, c_3546])).
% 5.80/2.09  tff(c_2506, plain, (![C_202]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_202, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_202, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_202))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_2502])).
% 5.80/2.09  tff(c_3583, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3556, c_2506])).
% 5.80/2.09  tff(c_3639, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_2993, c_2311, c_3583])).
% 5.80/2.09  tff(c_3680, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitLeft, [status(thm)], [c_3639])).
% 5.80/2.09  tff(c_3683, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_3680])).
% 5.80/2.09  tff(c_3687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_402, c_58, c_401, c_3683])).
% 5.80/2.09  tff(c_3689, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_3639])).
% 5.80/2.09  tff(c_54, plain, (![A_36, B_37, C_38]: (k2_tops_2(A_36, B_37, C_38)=k2_funct_1(C_38) | ~v2_funct_1(C_38) | k2_relset_1(A_36, B_37, C_38)!=B_37 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(C_38, A_36, B_37) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.80/2.09  tff(c_3722, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3689, c_54])).
% 5.80/2.09  tff(c_3780, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1803, c_1908, c_2993, c_1862, c_3722])).
% 5.80/2.09  tff(c_1988, plain, (![A_187, B_188, C_189]: (k2_tops_2(A_187, B_188, C_189)=k2_funct_1(C_189) | ~v2_funct_1(C_189) | k2_relset_1(A_187, B_188, C_189)!=B_188 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(C_189, A_187, B_188) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.80/2.09  tff(c_1991, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_1988])).
% 5.80/2.09  tff(c_1994, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403, c_401, c_58, c_1991])).
% 5.80/2.09  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.80/2.09  tff(c_173, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_83, c_82, c_82, c_82, c_56])).
% 5.80/2.09  tff(c_325, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_323, c_323, c_173])).
% 5.80/2.09  tff(c_469, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_396, c_396, c_325])).
% 5.80/2.09  tff(c_1995, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_469])).
% 5.80/2.09  tff(c_3843, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3780, c_1995])).
% 5.80/2.09  tff(c_3850, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_3843])).
% 5.80/2.09  tff(c_3853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_58, c_2519, c_3850])).
% 5.80/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.09  
% 5.80/2.09  Inference rules
% 5.80/2.09  ----------------------
% 5.80/2.09  #Ref     : 0
% 5.80/2.09  #Sup     : 815
% 5.80/2.09  #Fact    : 0
% 5.80/2.09  #Define  : 0
% 5.80/2.09  #Split   : 23
% 5.80/2.09  #Chain   : 0
% 5.80/2.09  #Close   : 0
% 5.80/2.09  
% 5.80/2.09  Ordering : KBO
% 5.80/2.09  
% 5.80/2.09  Simplification rules
% 5.80/2.09  ----------------------
% 5.80/2.09  #Subsume      : 42
% 5.80/2.09  #Demod        : 2136
% 5.80/2.09  #Tautology    : 471
% 5.80/2.09  #SimpNegUnit  : 10
% 5.80/2.09  #BackRed      : 48
% 5.80/2.09  
% 5.80/2.09  #Partial instantiations: 0
% 5.80/2.09  #Strategies tried      : 1
% 5.80/2.09  
% 5.80/2.09  Timing (in seconds)
% 5.80/2.09  ----------------------
% 5.80/2.10  Preprocessing        : 0.36
% 5.80/2.10  Parsing              : 0.19
% 5.80/2.10  CNF conversion       : 0.02
% 5.80/2.10  Main loop            : 0.93
% 5.80/2.10  Inferencing          : 0.32
% 5.80/2.10  Reduction            : 0.34
% 5.80/2.10  Demodulation         : 0.26
% 5.80/2.10  BG Simplification    : 0.04
% 5.80/2.10  Subsumption          : 0.15
% 5.80/2.10  Abstraction          : 0.05
% 5.80/2.10  MUC search           : 0.00
% 5.80/2.10  Cooper               : 0.00
% 5.80/2.10  Total                : 1.36
% 5.80/2.10  Index Insertion      : 0.00
% 5.80/2.10  Index Deletion       : 0.00
% 5.80/2.10  Index Matching       : 0.00
% 5.80/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
