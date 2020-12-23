%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:36 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :  206 (136929 expanded)
%              Number of leaves         :   49 (47411 expanded)
%              Depth                    :   35
%              Number of atoms          :  527 (391744 expanded)
%              Number of equality atoms :   95 (84443 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_252,negated_conjecture,(
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

tff(f_210,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_218,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_162,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_178,axiom,(
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

tff(f_194,axiom,(
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
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_206,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_130,axiom,(
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

tff(f_230,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_92,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_96,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_104,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_92,c_96])).

tff(c_88,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_103,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_96])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_135,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_103,c_82])).

tff(c_192,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_196,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_192])).

tff(c_80,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_130,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_103,c_80])).

tff(c_197,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_130])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_116,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_122,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_116])).

tff(c_126,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_122])).

tff(c_127,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_126])).

tff(c_206,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_127])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_136,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_135,c_136])).

tff(c_142,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_139])).

tff(c_156,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_160,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_135,c_156])).

tff(c_184,plain,(
    ! [B_71,A_72] :
      ( k1_relat_1(B_71) = A_72
      | ~ v1_partfun1(B_71,A_72)
      | ~ v4_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_187,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_184])).

tff(c_190,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_187])).

tff(c_191,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_109,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_84])).

tff(c_110,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_109])).

tff(c_207,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_110])).

tff(c_205,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_135])).

tff(c_373,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_partfun1(C_99,A_100)
      | ~ v1_funct_2(C_99,A_100,B_101)
      | ~ v1_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | v1_xboole_0(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_379,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_205,c_373])).

tff(c_383,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_207,c_379])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_191,c_383])).

tff(c_386,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_390,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_135])).

tff(c_44,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_436,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_390,c_44])).

tff(c_391,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_130])).

tff(c_448,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_391])).

tff(c_393,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_110])).

tff(c_454,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_393])).

tff(c_455,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_390])).

tff(c_627,plain,(
    ! [A_125,B_126,D_127] :
      ( r2_funct_2(A_125,B_126,D_127,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(D_127,A_125,B_126)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_631,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_627])).

tff(c_635,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_454,c_631])).

tff(c_78,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_453,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_436])).

tff(c_694,plain,(
    ! [C_141,A_142,B_143] :
      ( v1_funct_1(k2_funct_1(C_141))
      | k2_relset_1(A_142,B_143,C_141) != B_143
      | ~ v2_funct_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_2(C_141,A_142,B_143)
      | ~ v1_funct_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_700,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_694])).

tff(c_704,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_454,c_78,c_453,c_700])).

tff(c_749,plain,(
    ! [C_152,B_153,A_154] :
      ( v1_funct_2(k2_funct_1(C_152),B_153,A_154)
      | k2_relset_1(A_154,B_153,C_152) != B_153
      | ~ v2_funct_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153)))
      | ~ v1_funct_2(C_152,A_154,B_153)
      | ~ v1_funct_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_755,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_749])).

tff(c_759,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_454,c_78,c_453,c_755])).

tff(c_780,plain,(
    ! [C_159,B_160,A_161] :
      ( m1_subset_1(k2_funct_1(C_159),k1_zfmisc_1(k2_zfmisc_1(B_160,A_161)))
      | k2_relset_1(A_161,B_160,C_159) != B_160
      | ~ v2_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_2(C_159,A_161,B_160)
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_806,plain,(
    ! [C_159,B_160,A_161] :
      ( v1_relat_1(k2_funct_1(C_159))
      | ~ v1_relat_1(k2_zfmisc_1(B_160,A_161))
      | k2_relset_1(A_161,B_160,C_159) != B_160
      | ~ v2_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_2(C_159,A_161,B_160)
      | ~ v1_funct_1(C_159) ) ),
    inference(resolution,[status(thm)],[c_780,c_8])).

tff(c_818,plain,(
    ! [C_162,A_163,B_164] :
      ( v1_relat_1(k2_funct_1(C_162))
      | k2_relset_1(A_163,B_164,C_162) != B_164
      | ~ v2_funct_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_2(C_162,A_163,B_164)
      | ~ v1_funct_1(C_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_806])).

tff(c_827,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_818])).

tff(c_832,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_454,c_78,c_453,c_827])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_9] :
      ( v2_funct_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_521,plain,(
    ! [B_109,A_110] :
      ( m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_109),A_110)))
      | ~ r1_tarski(k2_relat_1(B_109),A_110)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_42,plain,(
    ! [C_22,A_20,B_21] :
      ( v4_relat_1(C_22,A_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_556,plain,(
    ! [B_114,A_115] :
      ( v4_relat_1(B_114,k1_relat_1(B_114))
      | ~ r1_tarski(k2_relat_1(B_114),A_115)
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_521,c_42])).

tff(c_569,plain,(
    ! [B_118] :
      ( v4_relat_1(B_118,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_556])).

tff(c_50,plain,(
    ! [B_31] :
      ( v1_partfun1(B_31,k1_relat_1(B_31))
      | ~ v4_relat_1(B_31,k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_582,plain,(
    ! [B_119] :
      ( v1_partfun1(B_119,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_569,c_50])).

tff(c_585,plain,(
    ! [A_15] :
      ( v1_partfun1(k2_funct_1(A_15),k2_relat_1(A_15))
      | ~ v1_funct_1(k2_funct_1(A_15))
      | ~ v1_relat_1(k2_funct_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_582])).

tff(c_833,plain,(
    ! [C_165,B_166,A_167] :
      ( v4_relat_1(k2_funct_1(C_165),B_166)
      | k2_relset_1(A_167,B_166,C_165) != B_166
      | ~ v2_funct_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166)))
      | ~ v1_funct_2(C_165,A_167,B_166)
      | ~ v1_funct_1(C_165) ) ),
    inference(resolution,[status(thm)],[c_780,c_42])).

tff(c_842,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_833])).

tff(c_847,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_454,c_78,c_453,c_842])).

tff(c_52,plain,(
    ! [B_31,A_30] :
      ( k1_relat_1(B_31) = A_30
      | ~ v1_partfun1(B_31,A_30)
      | ~ v4_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_850,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_847,c_52])).

tff(c_853,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_850])).

tff(c_854,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_853])).

tff(c_868,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_585,c_854])).

tff(c_872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_832,c_704,c_868])).

tff(c_873,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    ! [C_22,B_21,A_20] :
      ( v5_relat_1(C_22,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_543,plain,(
    ! [B_111,A_112] :
      ( v5_relat_1(B_111,A_112)
      | ~ r1_tarski(k2_relat_1(B_111),A_112)
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_521,c_40])).

tff(c_552,plain,(
    ! [B_113] :
      ( v5_relat_1(B_113,k2_relat_1(B_113))
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_543])).

tff(c_555,plain,(
    ! [A_15] :
      ( v5_relat_1(k2_funct_1(A_15),k1_relat_1(A_15))
      | ~ v1_funct_1(k2_funct_1(A_15))
      | ~ v1_relat_1(k2_funct_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_552])).

tff(c_890,plain,
    ( v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_555])).

tff(c_926,plain,
    ( v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_704,c_890])).

tff(c_1063,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_1066,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1063])).

tff(c_1070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_1066])).

tff(c_1071,plain,
    ( ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_1074,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1071])).

tff(c_1098,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1074])).

tff(c_1102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_704,c_1098])).

tff(c_1103,plain,
    ( ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_1105,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1103])).

tff(c_1115,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_1105])).

tff(c_1119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_704,c_1115])).

tff(c_1121,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1103])).

tff(c_1104,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_1072,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_586,plain,(
    ! [B_120,A_121] :
      ( k2_relset_1(k1_relat_1(B_120),A_121,B_120) = k2_relat_1(B_120)
      | ~ r1_tarski(k2_relat_1(B_120),A_121)
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_521,c_44])).

tff(c_592,plain,(
    ! [B_120] :
      ( k2_relset_1(k1_relat_1(B_120),k2_relat_1(B_120),B_120) = k2_relat_1(B_120)
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_586])).

tff(c_893,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_592])).

tff(c_928,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_704,c_893])).

tff(c_66,plain,(
    ! [B_40,A_39] :
      ( v1_funct_2(B_40,k1_relat_1(B_40),A_39)
      | ~ r1_tarski(k2_relat_1(B_40),A_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_64,plain,(
    ! [B_40,A_39] :
      ( m1_subset_1(B_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_40),A_39)))
      | ~ r1_tarski(k2_relat_1(B_40),A_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1290,plain,(
    ! [B_195,A_196] :
      ( v4_relat_1(k2_funct_1(B_195),A_196)
      | k2_relset_1(k1_relat_1(B_195),A_196,B_195) != A_196
      | ~ v2_funct_1(B_195)
      | ~ v1_funct_2(B_195,k1_relat_1(B_195),A_196)
      | ~ r1_tarski(k2_relat_1(B_195),A_196)
      | ~ v1_funct_1(B_195)
      | ~ v1_relat_1(B_195) ) ),
    inference(resolution,[status(thm)],[c_64,c_833])).

tff(c_1309,plain,(
    ! [B_197,A_198] :
      ( v4_relat_1(k2_funct_1(B_197),A_198)
      | k2_relset_1(k1_relat_1(B_197),A_198,B_197) != A_198
      | ~ v2_funct_1(B_197)
      | ~ r1_tarski(k2_relat_1(B_197),A_198)
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(resolution,[status(thm)],[c_66,c_1290])).

tff(c_1311,plain,(
    ! [A_198] :
      ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_198)
      | k2_relset_1(k2_relat_1('#skF_3'),A_198,k2_funct_1('#skF_3')) != A_198
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_198)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_1309])).

tff(c_1328,plain,(
    ! [A_199] :
      ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_199)
      | k2_relset_1(k2_relat_1('#skF_3'),A_199,k2_funct_1('#skF_3')) != A_199
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_704,c_1072,c_1311])).

tff(c_1331,plain,(
    ! [A_199] :
      ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = A_199
      | ~ v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),A_199)
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
      | k2_relset_1(k2_relat_1('#skF_3'),A_199,k2_funct_1('#skF_3')) != A_199
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_199) ) ),
    inference(resolution,[status(thm)],[c_1328,c_52])).

tff(c_2583,plain,(
    ! [A_239] :
      ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = A_239
      | ~ v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),A_239)
      | k2_relset_1(k2_relat_1('#skF_3'),A_239,k2_funct_1('#skF_3')) != A_239
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1331])).

tff(c_2591,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) != k2_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_585,c_2583])).

tff(c_2602,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_704,c_1072,c_1121,c_1104,c_6,c_928,c_2591])).

tff(c_581,plain,(
    ! [B_118] :
      ( v1_partfun1(B_118,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_569,c_50])).

tff(c_2651,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2602,c_581])).

tff(c_2697,plain,(
    v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1104,c_2651])).

tff(c_2734,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2697])).

tff(c_2736,plain,(
    v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_2734])).

tff(c_561,plain,(
    ! [B_114] :
      ( v4_relat_1(B_114,k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_6,c_556])).

tff(c_2654,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2602,c_561])).

tff(c_2699,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1104,c_2654])).

tff(c_2742,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2699])).

tff(c_2747,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_2742])).

tff(c_2750,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2747,c_52])).

tff(c_2753,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_2736,c_2602,c_2750])).

tff(c_593,plain,(
    ! [B_122] :
      ( k2_relset_1(k1_relat_1(B_122),k2_relat_1(B_122),B_122) = k2_relat_1(B_122)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_586])).

tff(c_608,plain,(
    ! [A_15] :
      ( k2_relset_1(k1_relat_1(k2_funct_1(A_15)),k1_relat_1(A_15),k2_funct_1(A_15)) = k2_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(k2_funct_1(A_15))
      | ~ v1_relat_1(k2_funct_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_593])).

tff(c_878,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_608])).

tff(c_918,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_832,c_704,c_878])).

tff(c_2771,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2753,c_918])).

tff(c_36,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k2_funct_1(A_16)) = k6_relat_1(k1_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_706,plain,(
    ! [A_146,B_147] :
      ( k2_funct_1(A_146) = B_147
      | k6_relat_1(k2_relat_1(A_146)) != k5_relat_1(B_147,A_146)
      | k2_relat_1(B_147) != k1_relat_1(A_146)
      | ~ v2_funct_1(A_146)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3039,plain,(
    ! [A_250] :
      ( k2_funct_1(k2_funct_1(A_250)) = A_250
      | k6_relat_1(k2_relat_1(k2_funct_1(A_250))) != k6_relat_1(k1_relat_1(A_250))
      | k1_relat_1(k2_funct_1(A_250)) != k2_relat_1(A_250)
      | ~ v2_funct_1(k2_funct_1(A_250))
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250)
      | ~ v1_funct_1(k2_funct_1(A_250))
      | ~ v1_relat_1(k2_funct_1(A_250))
      | ~ v2_funct_1(A_250)
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_706])).

tff(c_3042,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2753,c_3039])).

tff(c_3051,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_832,c_704,c_1072,c_873,c_3042])).

tff(c_74,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_tops_2(A_43,B_44,C_45) = k2_funct_1(C_45)
      | ~ v2_funct_1(C_45)
      | k2_relset_1(A_43,B_44,C_45) != B_44
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(C_45,A_43,B_44)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_3631,plain,(
    ! [B_267,A_268,C_269] :
      ( k2_tops_2(B_267,A_268,k2_funct_1(C_269)) = k2_funct_1(k2_funct_1(C_269))
      | ~ v2_funct_1(k2_funct_1(C_269))
      | k2_relset_1(B_267,A_268,k2_funct_1(C_269)) != A_268
      | ~ v1_funct_2(k2_funct_1(C_269),B_267,A_268)
      | ~ v1_funct_1(k2_funct_1(C_269))
      | k2_relset_1(A_268,B_267,C_269) != B_267
      | ~ v2_funct_1(C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_268,B_267)))
      | ~ v1_funct_2(C_269,A_268,B_267)
      | ~ v1_funct_1(C_269) ) ),
    inference(resolution,[status(thm)],[c_780,c_74])).

tff(c_3649,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_3631])).

tff(c_3661,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_454,c_78,c_453,c_704,c_759,c_2771,c_1072,c_3051,c_3649])).

tff(c_760,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_tops_2(A_155,B_156,C_157) = k2_funct_1(C_157)
      | ~ v2_funct_1(C_157)
      | k2_relset_1(A_155,B_156,C_157) != B_156
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_2(C_157,A_155,B_156)
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_766,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_760])).

tff(c_770,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_454,c_453,c_78,c_766])).

tff(c_76,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_162,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_104,c_104,c_103,c_103,c_103,c_76])).

tff(c_388,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_386,c_386,c_162])).

tff(c_482,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_448,c_448,c_388])).

tff(c_771,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_482])).

tff(c_3662,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3661,c_771])).

tff(c_3665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_3662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:10:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.05  
% 5.97/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.06  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.97/2.06  
% 5.97/2.06  %Foreground sorts:
% 5.97/2.06  
% 5.97/2.06  
% 5.97/2.06  %Background operators:
% 5.97/2.06  
% 5.97/2.06  
% 5.97/2.06  %Foreground operators:
% 5.97/2.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.97/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.97/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.97/2.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.97/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.97/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.97/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.97/2.06  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.97/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.97/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.97/2.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.97/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.97/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.97/2.06  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.97/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.97/2.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.97/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.97/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.97/2.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.97/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.97/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.97/2.06  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.97/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.97/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.97/2.06  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.97/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.97/2.06  
% 6.04/2.08  tff(f_252, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 6.04/2.08  tff(f_210, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.04/2.08  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.04/2.08  tff(f_218, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.04/2.08  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.04/2.08  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.04/2.08  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.04/2.08  tff(f_162, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 6.04/2.08  tff(f_154, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 6.04/2.08  tff(f_178, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 6.04/2.08  tff(f_194, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.04/2.08  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.04/2.08  tff(f_60, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 6.04/2.08  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.04/2.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.04/2.08  tff(f_206, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.04/2.08  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 6.04/2.08  tff(f_130, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 6.04/2.08  tff(f_230, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 6.04/2.08  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_92, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_96, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.04/2.08  tff(c_104, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_92, c_96])).
% 6.04/2.08  tff(c_88, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_103, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_88, c_96])).
% 6.04/2.08  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_135, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_103, c_82])).
% 6.04/2.08  tff(c_192, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.04/2.08  tff(c_196, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_192])).
% 6.04/2.08  tff(c_80, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_130, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_103, c_80])).
% 6.04/2.08  tff(c_197, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_130])).
% 6.04/2.08  tff(c_90, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_116, plain, (![A_55]: (~v1_xboole_0(u1_struct_0(A_55)) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_218])).
% 6.04/2.08  tff(c_122, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103, c_116])).
% 6.04/2.08  tff(c_126, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_122])).
% 6.04/2.08  tff(c_127, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_90, c_126])).
% 6.04/2.08  tff(c_206, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_127])).
% 6.04/2.08  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.04/2.08  tff(c_136, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.04/2.08  tff(c_139, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_135, c_136])).
% 6.04/2.08  tff(c_142, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_139])).
% 6.04/2.08  tff(c_156, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.04/2.08  tff(c_160, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_135, c_156])).
% 6.04/2.08  tff(c_184, plain, (![B_71, A_72]: (k1_relat_1(B_71)=A_72 | ~v1_partfun1(B_71, A_72) | ~v4_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.04/2.08  tff(c_187, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_184])).
% 6.04/2.08  tff(c_190, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_187])).
% 6.04/2.08  tff(c_191, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_190])).
% 6.04/2.08  tff(c_84, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_109, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_84])).
% 6.04/2.08  tff(c_110, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_109])).
% 6.04/2.08  tff(c_207, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_110])).
% 6.04/2.08  tff(c_205, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_135])).
% 6.04/2.08  tff(c_373, plain, (![C_99, A_100, B_101]: (v1_partfun1(C_99, A_100) | ~v1_funct_2(C_99, A_100, B_101) | ~v1_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | v1_xboole_0(B_101))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.04/2.08  tff(c_379, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_205, c_373])).
% 6.04/2.08  tff(c_383, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_207, c_379])).
% 6.04/2.08  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_191, c_383])).
% 6.04/2.08  tff(c_386, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_190])).
% 6.04/2.08  tff(c_390, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_135])).
% 6.04/2.08  tff(c_44, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.04/2.08  tff(c_436, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_390, c_44])).
% 6.04/2.08  tff(c_391, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_130])).
% 6.04/2.08  tff(c_448, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_391])).
% 6.04/2.08  tff(c_393, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_110])).
% 6.04/2.08  tff(c_454, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_393])).
% 6.04/2.08  tff(c_455, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_390])).
% 6.04/2.08  tff(c_627, plain, (![A_125, B_126, D_127]: (r2_funct_2(A_125, B_126, D_127, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(D_127, A_125, B_126) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.04/2.08  tff(c_631, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_627])).
% 6.04/2.08  tff(c_635, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_454, c_631])).
% 6.04/2.08  tff(c_78, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.08  tff(c_453, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_436])).
% 6.04/2.08  tff(c_694, plain, (![C_141, A_142, B_143]: (v1_funct_1(k2_funct_1(C_141)) | k2_relset_1(A_142, B_143, C_141)!=B_143 | ~v2_funct_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_2(C_141, A_142, B_143) | ~v1_funct_1(C_141))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.04/2.08  tff(c_700, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_694])).
% 6.04/2.08  tff(c_704, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_454, c_78, c_453, c_700])).
% 6.04/2.08  tff(c_749, plain, (![C_152, B_153, A_154]: (v1_funct_2(k2_funct_1(C_152), B_153, A_154) | k2_relset_1(A_154, B_153, C_152)!=B_153 | ~v2_funct_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))) | ~v1_funct_2(C_152, A_154, B_153) | ~v1_funct_1(C_152))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.04/2.08  tff(c_755, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_749])).
% 6.04/2.08  tff(c_759, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_454, c_78, c_453, c_755])).
% 6.04/2.08  tff(c_780, plain, (![C_159, B_160, A_161]: (m1_subset_1(k2_funct_1(C_159), k1_zfmisc_1(k2_zfmisc_1(B_160, A_161))) | k2_relset_1(A_161, B_160, C_159)!=B_160 | ~v2_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))) | ~v1_funct_2(C_159, A_161, B_160) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.04/2.08  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.04/2.08  tff(c_806, plain, (![C_159, B_160, A_161]: (v1_relat_1(k2_funct_1(C_159)) | ~v1_relat_1(k2_zfmisc_1(B_160, A_161)) | k2_relset_1(A_161, B_160, C_159)!=B_160 | ~v2_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))) | ~v1_funct_2(C_159, A_161, B_160) | ~v1_funct_1(C_159))), inference(resolution, [status(thm)], [c_780, c_8])).
% 6.04/2.08  tff(c_818, plain, (![C_162, A_163, B_164]: (v1_relat_1(k2_funct_1(C_162)) | k2_relset_1(A_163, B_164, C_162)!=B_164 | ~v2_funct_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_2(C_162, A_163, B_164) | ~v1_funct_1(C_162))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_806])).
% 6.04/2.08  tff(c_827, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_818])).
% 6.04/2.08  tff(c_832, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_454, c_78, c_453, c_827])).
% 6.04/2.08  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.04/2.08  tff(c_12, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.04/2.08  tff(c_16, plain, (![A_9]: (v2_funct_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.04/2.08  tff(c_32, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.04/2.08  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.04/2.08  tff(c_521, plain, (![B_109, A_110]: (m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_109), A_110))) | ~r1_tarski(k2_relat_1(B_109), A_110) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.04/2.08  tff(c_42, plain, (![C_22, A_20, B_21]: (v4_relat_1(C_22, A_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.04/2.08  tff(c_556, plain, (![B_114, A_115]: (v4_relat_1(B_114, k1_relat_1(B_114)) | ~r1_tarski(k2_relat_1(B_114), A_115) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_521, c_42])).
% 6.04/2.08  tff(c_569, plain, (![B_118]: (v4_relat_1(B_118, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_6, c_556])).
% 6.04/2.08  tff(c_50, plain, (![B_31]: (v1_partfun1(B_31, k1_relat_1(B_31)) | ~v4_relat_1(B_31, k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.04/2.08  tff(c_582, plain, (![B_119]: (v1_partfun1(B_119, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_569, c_50])).
% 6.04/2.08  tff(c_585, plain, (![A_15]: (v1_partfun1(k2_funct_1(A_15), k2_relat_1(A_15)) | ~v1_funct_1(k2_funct_1(A_15)) | ~v1_relat_1(k2_funct_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_32, c_582])).
% 6.04/2.08  tff(c_833, plain, (![C_165, B_166, A_167]: (v4_relat_1(k2_funct_1(C_165), B_166) | k2_relset_1(A_167, B_166, C_165)!=B_166 | ~v2_funct_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))) | ~v1_funct_2(C_165, A_167, B_166) | ~v1_funct_1(C_165))), inference(resolution, [status(thm)], [c_780, c_42])).
% 6.04/2.08  tff(c_842, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_833])).
% 6.04/2.08  tff(c_847, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_454, c_78, c_453, c_842])).
% 6.04/2.08  tff(c_52, plain, (![B_31, A_30]: (k1_relat_1(B_31)=A_30 | ~v1_partfun1(B_31, A_30) | ~v4_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.04/2.08  tff(c_850, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_847, c_52])).
% 6.04/2.08  tff(c_853, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_832, c_850])).
% 6.04/2.08  tff(c_854, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_853])).
% 6.04/2.08  tff(c_868, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_585, c_854])).
% 6.04/2.08  tff(c_872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_832, c_704, c_868])).
% 6.04/2.08  tff(c_873, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_853])).
% 6.04/2.08  tff(c_30, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.04/2.08  tff(c_40, plain, (![C_22, B_21, A_20]: (v5_relat_1(C_22, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.04/2.08  tff(c_543, plain, (![B_111, A_112]: (v5_relat_1(B_111, A_112) | ~r1_tarski(k2_relat_1(B_111), A_112) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_521, c_40])).
% 6.04/2.08  tff(c_552, plain, (![B_113]: (v5_relat_1(B_113, k2_relat_1(B_113)) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_6, c_543])).
% 6.04/2.08  tff(c_555, plain, (![A_15]: (v5_relat_1(k2_funct_1(A_15), k1_relat_1(A_15)) | ~v1_funct_1(k2_funct_1(A_15)) | ~v1_relat_1(k2_funct_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_30, c_552])).
% 6.04/2.08  tff(c_890, plain, (v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_873, c_555])).
% 6.04/2.08  tff(c_926, plain, (v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_832, c_704, c_890])).
% 6.04/2.08  tff(c_1063, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_926])).
% 6.04/2.08  tff(c_1066, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1063])).
% 6.04/2.08  tff(c_1070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_1066])).
% 6.04/2.08  tff(c_1071, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_926])).
% 6.04/2.08  tff(c_1074, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1071])).
% 6.04/2.08  tff(c_1098, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1074])).
% 6.04/2.08  tff(c_1102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_832, c_704, c_1098])).
% 6.04/2.08  tff(c_1103, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | v5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1071])).
% 6.04/2.08  tff(c_1105, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1103])).
% 6.04/2.08  tff(c_1115, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_1105])).
% 6.04/2.08  tff(c_1119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_832, c_704, c_1115])).
% 6.04/2.08  tff(c_1121, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1103])).
% 6.04/2.08  tff(c_1104, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1071])).
% 6.04/2.08  tff(c_1072, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_926])).
% 6.04/2.08  tff(c_586, plain, (![B_120, A_121]: (k2_relset_1(k1_relat_1(B_120), A_121, B_120)=k2_relat_1(B_120) | ~r1_tarski(k2_relat_1(B_120), A_121) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_521, c_44])).
% 6.04/2.08  tff(c_592, plain, (![B_120]: (k2_relset_1(k1_relat_1(B_120), k2_relat_1(B_120), B_120)=k2_relat_1(B_120) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_6, c_586])).
% 6.04/2.08  tff(c_893, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_873, c_592])).
% 6.04/2.08  tff(c_928, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_832, c_704, c_893])).
% 6.04/2.08  tff(c_66, plain, (![B_40, A_39]: (v1_funct_2(B_40, k1_relat_1(B_40), A_39) | ~r1_tarski(k2_relat_1(B_40), A_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.04/2.08  tff(c_64, plain, (![B_40, A_39]: (m1_subset_1(B_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_40), A_39))) | ~r1_tarski(k2_relat_1(B_40), A_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.04/2.08  tff(c_1290, plain, (![B_195, A_196]: (v4_relat_1(k2_funct_1(B_195), A_196) | k2_relset_1(k1_relat_1(B_195), A_196, B_195)!=A_196 | ~v2_funct_1(B_195) | ~v1_funct_2(B_195, k1_relat_1(B_195), A_196) | ~r1_tarski(k2_relat_1(B_195), A_196) | ~v1_funct_1(B_195) | ~v1_relat_1(B_195))), inference(resolution, [status(thm)], [c_64, c_833])).
% 6.04/2.08  tff(c_1309, plain, (![B_197, A_198]: (v4_relat_1(k2_funct_1(B_197), A_198) | k2_relset_1(k1_relat_1(B_197), A_198, B_197)!=A_198 | ~v2_funct_1(B_197) | ~r1_tarski(k2_relat_1(B_197), A_198) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(resolution, [status(thm)], [c_66, c_1290])).
% 6.04/2.08  tff(c_1311, plain, (![A_198]: (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_198) | k2_relset_1(k2_relat_1('#skF_3'), A_198, k2_funct_1('#skF_3'))!=A_198 | ~v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_198) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_873, c_1309])).
% 6.04/2.08  tff(c_1328, plain, (![A_199]: (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_199) | k2_relset_1(k2_relat_1('#skF_3'), A_199, k2_funct_1('#skF_3'))!=A_199 | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_199))), inference(demodulation, [status(thm), theory('equality')], [c_832, c_704, c_1072, c_1311])).
% 6.04/2.08  tff(c_1331, plain, (![A_199]: (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=A_199 | ~v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), A_199) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), A_199, k2_funct_1('#skF_3'))!=A_199 | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_199))), inference(resolution, [status(thm)], [c_1328, c_52])).
% 6.04/2.08  tff(c_2583, plain, (![A_239]: (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=A_239 | ~v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), A_239) | k2_relset_1(k2_relat_1('#skF_3'), A_239, k2_funct_1('#skF_3'))!=A_239 | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_239))), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1331])).
% 6.04/2.08  tff(c_2591, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))!=k2_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_585, c_2583])).
% 6.04/2.08  tff(c_2602, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_832, c_704, c_1072, c_1121, c_1104, c_6, c_928, c_2591])).
% 6.04/2.08  tff(c_581, plain, (![B_118]: (v1_partfun1(B_118, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_569, c_50])).
% 6.04/2.08  tff(c_2651, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2602, c_581])).
% 6.04/2.08  tff(c_2697, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1104, c_2651])).
% 6.04/2.08  tff(c_2734, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2697])).
% 6.04/2.08  tff(c_2736, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_2734])).
% 6.04/2.08  tff(c_561, plain, (![B_114]: (v4_relat_1(B_114, k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_6, c_556])).
% 6.04/2.08  tff(c_2654, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2602, c_561])).
% 6.04/2.08  tff(c_2699, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1104, c_2654])).
% 6.04/2.08  tff(c_2742, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2699])).
% 6.04/2.08  tff(c_2747, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_2742])).
% 6.04/2.08  tff(c_2750, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2747, c_52])).
% 6.04/2.08  tff(c_2753, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_2736, c_2602, c_2750])).
% 6.04/2.08  tff(c_593, plain, (![B_122]: (k2_relset_1(k1_relat_1(B_122), k2_relat_1(B_122), B_122)=k2_relat_1(B_122) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_6, c_586])).
% 6.04/2.08  tff(c_608, plain, (![A_15]: (k2_relset_1(k1_relat_1(k2_funct_1(A_15)), k1_relat_1(A_15), k2_funct_1(A_15))=k2_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(k2_funct_1(A_15)) | ~v1_relat_1(k2_funct_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_30, c_593])).
% 6.04/2.08  tff(c_878, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_873, c_608])).
% 6.04/2.09  tff(c_918, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_832, c_704, c_878])).
% 6.04/2.09  tff(c_2771, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2753, c_918])).
% 6.04/2.09  tff(c_36, plain, (![A_16]: (k5_relat_1(A_16, k2_funct_1(A_16))=k6_relat_1(k1_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.04/2.09  tff(c_706, plain, (![A_146, B_147]: (k2_funct_1(A_146)=B_147 | k6_relat_1(k2_relat_1(A_146))!=k5_relat_1(B_147, A_146) | k2_relat_1(B_147)!=k1_relat_1(A_146) | ~v2_funct_1(A_146) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.04/2.09  tff(c_3039, plain, (![A_250]: (k2_funct_1(k2_funct_1(A_250))=A_250 | k6_relat_1(k2_relat_1(k2_funct_1(A_250)))!=k6_relat_1(k1_relat_1(A_250)) | k1_relat_1(k2_funct_1(A_250))!=k2_relat_1(A_250) | ~v2_funct_1(k2_funct_1(A_250)) | ~v1_funct_1(A_250) | ~v1_relat_1(A_250) | ~v1_funct_1(k2_funct_1(A_250)) | ~v1_relat_1(k2_funct_1(A_250)) | ~v2_funct_1(A_250) | ~v1_funct_1(A_250) | ~v1_relat_1(A_250))), inference(superposition, [status(thm), theory('equality')], [c_36, c_706])).
% 6.04/2.09  tff(c_3042, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2753, c_3039])).
% 6.04/2.09  tff(c_3051, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_832, c_704, c_1072, c_873, c_3042])).
% 6.04/2.09  tff(c_74, plain, (![A_43, B_44, C_45]: (k2_tops_2(A_43, B_44, C_45)=k2_funct_1(C_45) | ~v2_funct_1(C_45) | k2_relset_1(A_43, B_44, C_45)!=B_44 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(C_45, A_43, B_44) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_230])).
% 6.04/2.09  tff(c_3631, plain, (![B_267, A_268, C_269]: (k2_tops_2(B_267, A_268, k2_funct_1(C_269))=k2_funct_1(k2_funct_1(C_269)) | ~v2_funct_1(k2_funct_1(C_269)) | k2_relset_1(B_267, A_268, k2_funct_1(C_269))!=A_268 | ~v1_funct_2(k2_funct_1(C_269), B_267, A_268) | ~v1_funct_1(k2_funct_1(C_269)) | k2_relset_1(A_268, B_267, C_269)!=B_267 | ~v2_funct_1(C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_268, B_267))) | ~v1_funct_2(C_269, A_268, B_267) | ~v1_funct_1(C_269))), inference(resolution, [status(thm)], [c_780, c_74])).
% 6.04/2.09  tff(c_3649, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_3631])).
% 6.04/2.09  tff(c_3661, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_454, c_78, c_453, c_704, c_759, c_2771, c_1072, c_3051, c_3649])).
% 6.04/2.09  tff(c_760, plain, (![A_155, B_156, C_157]: (k2_tops_2(A_155, B_156, C_157)=k2_funct_1(C_157) | ~v2_funct_1(C_157) | k2_relset_1(A_155, B_156, C_157)!=B_156 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_2(C_157, A_155, B_156) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_230])).
% 6.04/2.09  tff(c_766, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_760])).
% 6.04/2.09  tff(c_770, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_454, c_453, c_78, c_766])).
% 6.04/2.09  tff(c_76, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.04/2.09  tff(c_162, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_104, c_104, c_103, c_103, c_103, c_76])).
% 6.04/2.09  tff(c_388, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_386, c_386, c_162])).
% 6.04/2.09  tff(c_482, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_448, c_448, c_388])).
% 6.04/2.09  tff(c_771, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_770, c_482])).
% 6.04/2.09  tff(c_3662, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3661, c_771])).
% 6.04/2.09  tff(c_3665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_635, c_3662])).
% 6.04/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.09  
% 6.04/2.09  Inference rules
% 6.04/2.09  ----------------------
% 6.04/2.09  #Ref     : 0
% 6.04/2.09  #Sup     : 696
% 6.04/2.09  #Fact    : 0
% 6.04/2.09  #Define  : 0
% 6.04/2.09  #Split   : 11
% 6.04/2.09  #Chain   : 0
% 6.04/2.09  #Close   : 0
% 6.04/2.09  
% 6.04/2.09  Ordering : KBO
% 6.04/2.09  
% 6.04/2.09  Simplification rules
% 6.04/2.09  ----------------------
% 6.04/2.09  #Subsume      : 57
% 6.04/2.09  #Demod        : 1959
% 6.04/2.09  #Tautology    : 395
% 6.04/2.09  #SimpNegUnit  : 12
% 6.04/2.09  #BackRed      : 98
% 6.04/2.09  
% 6.04/2.09  #Partial instantiations: 0
% 6.04/2.09  #Strategies tried      : 1
% 6.04/2.09  
% 6.04/2.09  Timing (in seconds)
% 6.04/2.09  ----------------------
% 6.04/2.09  Preprocessing        : 0.38
% 6.04/2.09  Parsing              : 0.20
% 6.04/2.09  CNF conversion       : 0.03
% 6.04/2.09  Main loop            : 0.92
% 6.04/2.09  Inferencing          : 0.30
% 6.04/2.09  Reduction            : 0.34
% 6.04/2.09  Demodulation         : 0.24
% 6.04/2.09  BG Simplification    : 0.04
% 6.04/2.09  Subsumption          : 0.18
% 6.04/2.09  Abstraction          : 0.04
% 6.04/2.09  MUC search           : 0.00
% 6.04/2.09  Cooper               : 0.00
% 6.04/2.09  Total                : 1.36
% 6.04/2.09  Index Insertion      : 0.00
% 6.04/2.09  Index Deletion       : 0.00
% 6.04/2.09  Index Matching       : 0.00
% 6.04/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
