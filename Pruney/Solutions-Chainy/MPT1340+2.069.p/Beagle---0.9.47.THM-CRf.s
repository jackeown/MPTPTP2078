%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:40 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  163 (22962 expanded)
%              Number of leaves         :   46 (7984 expanded)
%              Depth                    :   24
%              Number of atoms          :  433 (65881 expanded)
%              Number of equality atoms :   90 (14251 expanded)
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

tff(f_208,negated_conjecture,(
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

tff(f_166,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

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

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_146,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_162,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_63,axiom,(
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

tff(f_100,axiom,(
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

tff(f_186,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_72,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_76,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_84,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_76])).

tff(c_83,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_76])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_103,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_62])).

tff(c_152,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_156,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_152])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_98,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_60])).

tff(c_157,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_98])).

tff(c_52,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k2_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_171,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_52])).

tff(c_175,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_171])).

tff(c_176,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_175])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_103,c_104])).

tff(c_110,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_117,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_121,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_103,c_117])).

tff(c_144,plain,(
    ! [B_63,A_64] :
      ( k1_relat_1(B_63) = A_64
      | ~ v1_partfun1(B_63,A_64)
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_147,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_144])).

tff(c_150,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_147])).

tff(c_151,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_85,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_64])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_85])).

tff(c_166,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_94])).

tff(c_165,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_103])).

tff(c_225,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_partfun1(C_70,A_71)
      | ~ v1_funct_2(C_70,A_71,B_72)
      | ~ v1_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | v1_xboole_0(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_228,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_165,c_225])).

tff(c_231,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_166,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_151,c_231])).

tff(c_234,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_238,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_103])).

tff(c_32,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_282,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_32])).

tff(c_239,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_98])).

tff(c_295,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_239])).

tff(c_240,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_94])).

tff(c_310,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_240])).

tff(c_311,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_238])).

tff(c_495,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_funct_2(A_109,B_110,C_111,C_111)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_2(D_112,A_109,B_110)
      | ~ v1_funct_1(D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_2(C_111,A_109,B_110)
      | ~ v1_funct_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_499,plain,(
    ! [C_111] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_111,C_111)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_111,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_311,c_495])).

tff(c_527,plain,(
    ! [C_116] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_116,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_116,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_499])).

tff(c_532,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_527])).

tff(c_536,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_532])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_309,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_282])).

tff(c_393,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_funct_1(k2_funct_1(C_85))
      | k2_relset_1(A_86,B_87,C_85) != B_87
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(C_85,A_86,B_87)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_396,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_393])).

tff(c_399,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_58,c_309,c_396])).

tff(c_415,plain,(
    ! [C_93,B_94,A_95] :
      ( v1_funct_2(k2_funct_1(C_93),B_94,A_95)
      | k2_relset_1(A_95,B_94,C_93) != B_94
      | ~ v2_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94)))
      | ~ v1_funct_2(C_93,A_95,B_94)
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_418,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_415])).

tff(c_421,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_58,c_309,c_418])).

tff(c_438,plain,(
    ! [C_100,B_101,A_102] :
      ( m1_subset_1(k2_funct_1(C_100),k1_zfmisc_1(k2_zfmisc_1(B_101,A_102)))
      | k2_relset_1(A_102,B_101,C_100) != B_101
      | ~ v2_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2(C_100,A_102,B_101)
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_462,plain,(
    ! [C_100,B_101,A_102] :
      ( v1_relat_1(k2_funct_1(C_100))
      | ~ v1_relat_1(k2_zfmisc_1(B_101,A_102))
      | k2_relset_1(A_102,B_101,C_100) != B_101
      | ~ v2_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2(C_100,A_102,B_101)
      | ~ v1_funct_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_438,c_2])).

tff(c_473,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_relat_1(k2_funct_1(C_103))
      | k2_relset_1(A_104,B_105,C_103) != B_105
      | ~ v2_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(C_103,A_104,B_105)
      | ~ v1_funct_1(C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_462])).

tff(c_479,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_473])).

tff(c_483,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_58,c_309,c_479])).

tff(c_30,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_504,plain,(
    ! [C_113,B_114,A_115] :
      ( v4_relat_1(k2_funct_1(C_113),B_114)
      | k2_relset_1(A_115,B_114,C_113) != B_114
      | ~ v2_funct_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_2(C_113,A_115,B_114)
      | ~ v1_funct_1(C_113) ) ),
    inference(resolution,[status(thm)],[c_438,c_30])).

tff(c_510,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_504])).

tff(c_514,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_58,c_309,c_510])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_123,plain,(
    ! [A_61] :
      ( k1_relat_1(k2_funct_1(A_61)) = k2_relat_1(A_61)
      | ~ v2_funct_1(A_61)
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    ! [B_27] :
      ( v1_partfun1(B_27,k1_relat_1(B_27))
      | ~ v4_relat_1(B_27,k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_400,plain,(
    ! [A_88] :
      ( v1_partfun1(k2_funct_1(A_88),k1_relat_1(k2_funct_1(A_88)))
      | ~ v4_relat_1(k2_funct_1(A_88),k2_relat_1(A_88))
      | ~ v1_relat_1(k2_funct_1(A_88))
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_38])).

tff(c_403,plain,(
    ! [A_11] :
      ( v1_partfun1(k2_funct_1(A_11),k2_relat_1(A_11))
      | ~ v4_relat_1(k2_funct_1(A_11),k2_relat_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_400])).

tff(c_517,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_514,c_403])).

tff(c_523,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_66,c_58,c_483,c_517])).

tff(c_40,plain,(
    ! [B_27,A_26] :
      ( k1_relat_1(B_27) = A_26
      | ~ v1_partfun1(B_27,A_26)
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_520,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_514,c_40])).

tff(c_526,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_520])).

tff(c_538,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_526])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_382,plain,(
    ! [A_83,B_84] :
      ( v2_funct_1(A_83)
      | k2_relat_1(B_84) != k1_relat_1(A_83)
      | ~ v2_funct_1(k5_relat_1(B_84,A_83))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_388,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k1_relat_1(k2_funct_1(A_12)) != k2_relat_1(A_12)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_12)))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_382])).

tff(c_392,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k1_relat_1(k2_funct_1(A_12)) != k2_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_388])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_406,plain,(
    ! [A_91,B_92] :
      ( k2_funct_1(A_91) = B_92
      | k6_relat_1(k2_relat_1(A_91)) != k5_relat_1(B_92,A_91)
      | k2_relat_1(B_92) != k1_relat_1(A_91)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_592,plain,(
    ! [A_123,B_124] :
      ( k2_funct_1(k2_funct_1(A_123)) = B_124
      | k5_relat_1(B_124,k2_funct_1(A_123)) != k6_relat_1(k1_relat_1(A_123))
      | k2_relat_1(B_124) != k1_relat_1(k2_funct_1(A_123))
      | ~ v2_funct_1(k2_funct_1(A_123))
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1(k2_funct_1(A_123))
      | ~ v1_relat_1(k2_funct_1(A_123))
      | ~ v2_funct_1(A_123)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_406])).

tff(c_600,plain,(
    ! [A_125] :
      ( k2_funct_1(k2_funct_1(A_125)) = A_125
      | k1_relat_1(k2_funct_1(A_125)) != k2_relat_1(A_125)
      | ~ v2_funct_1(k2_funct_1(A_125))
      | ~ v1_funct_1(k2_funct_1(A_125))
      | ~ v1_relat_1(k2_funct_1(A_125))
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_592])).

tff(c_609,plain,(
    ! [A_126] :
      ( k2_funct_1(k2_funct_1(A_126)) = A_126
      | k1_relat_1(k2_funct_1(A_126)) != k2_relat_1(A_126)
      | ~ v1_funct_1(k2_funct_1(A_126))
      | ~ v1_relat_1(k2_funct_1(A_126))
      | ~ v2_funct_1(A_126)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_392,c_600])).

tff(c_612,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_609])).

tff(c_618,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_66,c_58,c_399,c_538,c_612])).

tff(c_662,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_20])).

tff(c_698,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_399,c_662])).

tff(c_704,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_698])).

tff(c_707,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_392,c_704])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_66,c_58,c_483,c_399,c_538,c_707])).

tff(c_715,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_565,plain,(
    ! [B_117,A_118,C_119] :
      ( k2_relset_1(B_117,A_118,k2_funct_1(C_119)) = k2_relat_1(k2_funct_1(C_119))
      | k2_relset_1(A_118,B_117,C_119) != B_117
      | ~ v2_funct_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ v1_funct_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_438,c_32])).

tff(c_571,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_565])).

tff(c_575,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_58,c_309,c_571])).

tff(c_717,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_575])).

tff(c_716,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_54,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_tops_2(A_37,B_38,C_39) = k2_funct_1(C_39)
      | ~ v2_funct_1(C_39)
      | k2_relset_1(A_37,B_38,C_39) != B_38
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1386,plain,(
    ! [B_152,A_153,C_154] :
      ( k2_tops_2(B_152,A_153,k2_funct_1(C_154)) = k2_funct_1(k2_funct_1(C_154))
      | ~ v2_funct_1(k2_funct_1(C_154))
      | k2_relset_1(B_152,A_153,k2_funct_1(C_154)) != A_153
      | ~ v1_funct_2(k2_funct_1(C_154),B_152,A_153)
      | ~ v1_funct_1(k2_funct_1(C_154))
      | k2_relset_1(A_153,B_152,C_154) != B_152
      | ~ v2_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152)))
      | ~ v1_funct_2(C_154,A_153,B_152)
      | ~ v1_funct_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_438,c_54])).

tff(c_1392,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_1386])).

tff(c_1396,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_58,c_309,c_399,c_421,c_717,c_716,c_618,c_1392])).

tff(c_422,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_tops_2(A_96,B_97,C_98) = k2_funct_1(C_98)
      | ~ v2_funct_1(C_98)
      | k2_relset_1(A_96,B_97,C_98) != B_97
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_425,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_422])).

tff(c_428,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_310,c_309,c_58,c_425])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_111,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_84,c_83,c_83,c_83,c_56])).

tff(c_237,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_234,c_111])).

tff(c_370,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_295,c_295,c_237])).

tff(c_429,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_370])).

tff(c_1397,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_429])).

tff(c_1400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_1397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.81  
% 4.69/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.81  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.70/1.81  
% 4.70/1.81  %Foreground sorts:
% 4.70/1.81  
% 4.70/1.81  
% 4.70/1.81  %Background operators:
% 4.70/1.81  
% 4.70/1.81  
% 4.70/1.81  %Foreground operators:
% 4.70/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.70/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.70/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.70/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.70/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.70/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.70/1.81  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.70/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.70/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.70/1.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.70/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.70/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.70/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.81  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.70/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/1.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.70/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.70/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.70/1.81  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.70/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.70/1.81  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.70/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.81  
% 4.70/1.84  tff(f_208, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.70/1.84  tff(f_166, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.70/1.84  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.70/1.84  tff(f_174, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 4.70/1.84  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.70/1.84  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.70/1.84  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.70/1.84  tff(f_132, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.70/1.84  tff(f_124, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.70/1.84  tff(f_146, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.70/1.84  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.70/1.84  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.70/1.84  tff(f_46, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.70/1.84  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.70/1.84  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.70/1.84  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.70/1.84  tff(f_186, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.70/1.84  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_72, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_76, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.70/1.84  tff(c_84, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_76])).
% 4.70/1.84  tff(c_83, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_76])).
% 4.70/1.84  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_103, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_62])).
% 4.70/1.84  tff(c_152, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.70/1.84  tff(c_156, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_152])).
% 4.70/1.84  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_98, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_60])).
% 4.70/1.84  tff(c_157, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_98])).
% 4.70/1.84  tff(c_52, plain, (![A_36]: (~v1_xboole_0(k2_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_174])).
% 4.70/1.84  tff(c_171, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_157, c_52])).
% 4.70/1.84  tff(c_175, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_171])).
% 4.70/1.84  tff(c_176, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_175])).
% 4.70/1.84  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.70/1.84  tff(c_104, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.70/1.84  tff(c_107, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_103, c_104])).
% 4.70/1.84  tff(c_110, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_107])).
% 4.70/1.84  tff(c_117, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.70/1.84  tff(c_121, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_103, c_117])).
% 4.70/1.84  tff(c_144, plain, (![B_63, A_64]: (k1_relat_1(B_63)=A_64 | ~v1_partfun1(B_63, A_64) | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.70/1.84  tff(c_147, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_121, c_144])).
% 4.70/1.84  tff(c_150, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_147])).
% 4.70/1.84  tff(c_151, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_150])).
% 4.70/1.84  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_85, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_64])).
% 4.70/1.84  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_85])).
% 4.70/1.84  tff(c_166, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_94])).
% 4.70/1.84  tff(c_165, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_103])).
% 4.70/1.84  tff(c_225, plain, (![C_70, A_71, B_72]: (v1_partfun1(C_70, A_71) | ~v1_funct_2(C_70, A_71, B_72) | ~v1_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | v1_xboole_0(B_72))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.70/1.84  tff(c_228, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_165, c_225])).
% 4.70/1.84  tff(c_231, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_166, c_228])).
% 4.70/1.84  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_151, c_231])).
% 4.70/1.84  tff(c_234, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_150])).
% 4.70/1.84  tff(c_238, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_103])).
% 4.70/1.84  tff(c_32, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.70/1.84  tff(c_282, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_238, c_32])).
% 4.70/1.84  tff(c_239, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_98])).
% 4.70/1.84  tff(c_295, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_239])).
% 4.70/1.84  tff(c_240, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_94])).
% 4.70/1.84  tff(c_310, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_240])).
% 4.70/1.84  tff(c_311, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_238])).
% 4.70/1.84  tff(c_495, plain, (![A_109, B_110, C_111, D_112]: (r2_funct_2(A_109, B_110, C_111, C_111) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_2(D_112, A_109, B_110) | ~v1_funct_1(D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_2(C_111, A_109, B_110) | ~v1_funct_1(C_111))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.70/1.84  tff(c_499, plain, (![C_111]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_111, C_111) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_111, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_111))), inference(resolution, [status(thm)], [c_311, c_495])).
% 4.70/1.84  tff(c_527, plain, (![C_116]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_116, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_116, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_116))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_499])).
% 4.70/1.84  tff(c_532, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_527])).
% 4.70/1.84  tff(c_536, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_532])).
% 4.70/1.84  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_309, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_282])).
% 4.70/1.84  tff(c_393, plain, (![C_85, A_86, B_87]: (v1_funct_1(k2_funct_1(C_85)) | k2_relset_1(A_86, B_87, C_85)!=B_87 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(C_85, A_86, B_87) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.70/1.84  tff(c_396, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_393])).
% 4.70/1.84  tff(c_399, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_58, c_309, c_396])).
% 4.70/1.84  tff(c_415, plain, (![C_93, B_94, A_95]: (v1_funct_2(k2_funct_1(C_93), B_94, A_95) | k2_relset_1(A_95, B_94, C_93)!=B_94 | ~v2_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))) | ~v1_funct_2(C_93, A_95, B_94) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.70/1.84  tff(c_418, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_415])).
% 4.70/1.84  tff(c_421, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_58, c_309, c_418])).
% 4.70/1.84  tff(c_438, plain, (![C_100, B_101, A_102]: (m1_subset_1(k2_funct_1(C_100), k1_zfmisc_1(k2_zfmisc_1(B_101, A_102))) | k2_relset_1(A_102, B_101, C_100)!=B_101 | ~v2_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2(C_100, A_102, B_101) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.70/1.84  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.70/1.84  tff(c_462, plain, (![C_100, B_101, A_102]: (v1_relat_1(k2_funct_1(C_100)) | ~v1_relat_1(k2_zfmisc_1(B_101, A_102)) | k2_relset_1(A_102, B_101, C_100)!=B_101 | ~v2_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2(C_100, A_102, B_101) | ~v1_funct_1(C_100))), inference(resolution, [status(thm)], [c_438, c_2])).
% 4.70/1.84  tff(c_473, plain, (![C_103, A_104, B_105]: (v1_relat_1(k2_funct_1(C_103)) | k2_relset_1(A_104, B_105, C_103)!=B_105 | ~v2_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(C_103, A_104, B_105) | ~v1_funct_1(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_462])).
% 4.70/1.84  tff(c_479, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_473])).
% 4.70/1.84  tff(c_483, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_58, c_309, c_479])).
% 4.70/1.84  tff(c_30, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.70/1.84  tff(c_504, plain, (![C_113, B_114, A_115]: (v4_relat_1(k2_funct_1(C_113), B_114) | k2_relset_1(A_115, B_114, C_113)!=B_114 | ~v2_funct_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_2(C_113, A_115, B_114) | ~v1_funct_1(C_113))), inference(resolution, [status(thm)], [c_438, c_30])).
% 4.70/1.84  tff(c_510, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_504])).
% 4.70/1.84  tff(c_514, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_58, c_309, c_510])).
% 4.70/1.84  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.70/1.84  tff(c_123, plain, (![A_61]: (k1_relat_1(k2_funct_1(A_61))=k2_relat_1(A_61) | ~v2_funct_1(A_61) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.70/1.84  tff(c_38, plain, (![B_27]: (v1_partfun1(B_27, k1_relat_1(B_27)) | ~v4_relat_1(B_27, k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.70/1.84  tff(c_400, plain, (![A_88]: (v1_partfun1(k2_funct_1(A_88), k1_relat_1(k2_funct_1(A_88))) | ~v4_relat_1(k2_funct_1(A_88), k2_relat_1(A_88)) | ~v1_relat_1(k2_funct_1(A_88)) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_123, c_38])).
% 4.70/1.84  tff(c_403, plain, (![A_11]: (v1_partfun1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v4_relat_1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_400])).
% 4.70/1.84  tff(c_517, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_514, c_403])).
% 4.70/1.84  tff(c_523, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_66, c_58, c_483, c_517])).
% 4.70/1.84  tff(c_40, plain, (![B_27, A_26]: (k1_relat_1(B_27)=A_26 | ~v1_partfun1(B_27, A_26) | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.70/1.84  tff(c_520, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_514, c_40])).
% 4.70/1.84  tff(c_526, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_520])).
% 4.70/1.84  tff(c_538, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_526])).
% 4.70/1.84  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.70/1.84  tff(c_24, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.70/1.84  tff(c_382, plain, (![A_83, B_84]: (v2_funct_1(A_83) | k2_relat_1(B_84)!=k1_relat_1(A_83) | ~v2_funct_1(k5_relat_1(B_84, A_83)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.70/1.84  tff(c_388, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_12))) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_382])).
% 4.70/1.84  tff(c_392, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_388])).
% 4.70/1.84  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.70/1.84  tff(c_406, plain, (![A_91, B_92]: (k2_funct_1(A_91)=B_92 | k6_relat_1(k2_relat_1(A_91))!=k5_relat_1(B_92, A_91) | k2_relat_1(B_92)!=k1_relat_1(A_91) | ~v2_funct_1(A_91) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.70/1.84  tff(c_592, plain, (![A_123, B_124]: (k2_funct_1(k2_funct_1(A_123))=B_124 | k5_relat_1(B_124, k2_funct_1(A_123))!=k6_relat_1(k1_relat_1(A_123)) | k2_relat_1(B_124)!=k1_relat_1(k2_funct_1(A_123)) | ~v2_funct_1(k2_funct_1(A_123)) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1(k2_funct_1(A_123)) | ~v1_relat_1(k2_funct_1(A_123)) | ~v2_funct_1(A_123) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_18, c_406])).
% 4.70/1.84  tff(c_600, plain, (![A_125]: (k2_funct_1(k2_funct_1(A_125))=A_125 | k1_relat_1(k2_funct_1(A_125))!=k2_relat_1(A_125) | ~v2_funct_1(k2_funct_1(A_125)) | ~v1_funct_1(k2_funct_1(A_125)) | ~v1_relat_1(k2_funct_1(A_125)) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_24, c_592])).
% 4.70/1.84  tff(c_609, plain, (![A_126]: (k2_funct_1(k2_funct_1(A_126))=A_126 | k1_relat_1(k2_funct_1(A_126))!=k2_relat_1(A_126) | ~v1_funct_1(k2_funct_1(A_126)) | ~v1_relat_1(k2_funct_1(A_126)) | ~v2_funct_1(A_126) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_392, c_600])).
% 4.70/1.84  tff(c_612, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_609])).
% 4.70/1.84  tff(c_618, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_66, c_58, c_399, c_538, c_612])).
% 4.70/1.84  tff(c_662, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_618, c_20])).
% 4.70/1.84  tff(c_698, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_399, c_662])).
% 4.70/1.84  tff(c_704, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_698])).
% 4.70/1.84  tff(c_707, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_392, c_704])).
% 4.70/1.84  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_66, c_58, c_483, c_399, c_538, c_707])).
% 4.70/1.84  tff(c_715, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_698])).
% 4.70/1.84  tff(c_565, plain, (![B_117, A_118, C_119]: (k2_relset_1(B_117, A_118, k2_funct_1(C_119))=k2_relat_1(k2_funct_1(C_119)) | k2_relset_1(A_118, B_117, C_119)!=B_117 | ~v2_funct_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_2(C_119, A_118, B_117) | ~v1_funct_1(C_119))), inference(resolution, [status(thm)], [c_438, c_32])).
% 4.70/1.84  tff(c_571, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_565])).
% 4.70/1.84  tff(c_575, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_58, c_309, c_571])).
% 4.70/1.84  tff(c_717, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_715, c_575])).
% 4.70/1.84  tff(c_716, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_698])).
% 4.70/1.84  tff(c_54, plain, (![A_37, B_38, C_39]: (k2_tops_2(A_37, B_38, C_39)=k2_funct_1(C_39) | ~v2_funct_1(C_39) | k2_relset_1(A_37, B_38, C_39)!=B_38 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(C_39, A_37, B_38) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.70/1.84  tff(c_1386, plain, (![B_152, A_153, C_154]: (k2_tops_2(B_152, A_153, k2_funct_1(C_154))=k2_funct_1(k2_funct_1(C_154)) | ~v2_funct_1(k2_funct_1(C_154)) | k2_relset_1(B_152, A_153, k2_funct_1(C_154))!=A_153 | ~v1_funct_2(k2_funct_1(C_154), B_152, A_153) | ~v1_funct_1(k2_funct_1(C_154)) | k2_relset_1(A_153, B_152, C_154)!=B_152 | ~v2_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))) | ~v1_funct_2(C_154, A_153, B_152) | ~v1_funct_1(C_154))), inference(resolution, [status(thm)], [c_438, c_54])).
% 4.70/1.84  tff(c_1392, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_1386])).
% 4.70/1.84  tff(c_1396, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_58, c_309, c_399, c_421, c_717, c_716, c_618, c_1392])).
% 4.70/1.84  tff(c_422, plain, (![A_96, B_97, C_98]: (k2_tops_2(A_96, B_97, C_98)=k2_funct_1(C_98) | ~v2_funct_1(C_98) | k2_relset_1(A_96, B_97, C_98)!=B_97 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.70/1.84  tff(c_425, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_422])).
% 4.70/1.84  tff(c_428, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_310, c_309, c_58, c_425])).
% 4.70/1.84  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.70/1.84  tff(c_111, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84, c_84, c_83, c_83, c_83, c_56])).
% 4.70/1.84  tff(c_237, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_234, c_234, c_111])).
% 4.70/1.84  tff(c_370, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_295, c_295, c_237])).
% 4.70/1.84  tff(c_429, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_370])).
% 4.70/1.84  tff(c_1397, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_429])).
% 4.70/1.84  tff(c_1400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_536, c_1397])).
% 4.70/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.84  
% 4.70/1.84  Inference rules
% 4.70/1.84  ----------------------
% 4.70/1.84  #Ref     : 0
% 4.70/1.84  #Sup     : 301
% 4.70/1.84  #Fact    : 0
% 4.70/1.84  #Define  : 0
% 4.70/1.84  #Split   : 4
% 4.70/1.84  #Chain   : 0
% 4.70/1.84  #Close   : 0
% 4.70/1.84  
% 4.70/1.84  Ordering : KBO
% 4.70/1.84  
% 4.70/1.84  Simplification rules
% 4.70/1.84  ----------------------
% 4.70/1.84  #Subsume      : 25
% 4.70/1.84  #Demod        : 773
% 4.70/1.84  #Tautology    : 185
% 4.70/1.84  #SimpNegUnit  : 5
% 4.70/1.84  #BackRed      : 23
% 4.70/1.84  
% 4.70/1.84  #Partial instantiations: 0
% 4.70/1.84  #Strategies tried      : 1
% 4.70/1.84  
% 4.70/1.84  Timing (in seconds)
% 4.70/1.84  ----------------------
% 4.70/1.84  Preprocessing        : 0.38
% 4.70/1.84  Parsing              : 0.21
% 4.70/1.84  CNF conversion       : 0.02
% 4.70/1.84  Main loop            : 0.61
% 4.70/1.84  Inferencing          : 0.22
% 4.70/1.84  Reduction            : 0.22
% 4.70/1.84  Demodulation         : 0.16
% 4.70/1.84  BG Simplification    : 0.03
% 4.70/1.84  Subsumption          : 0.10
% 4.70/1.84  Abstraction          : 0.03
% 4.70/1.84  MUC search           : 0.00
% 4.70/1.84  Cooper               : 0.00
% 4.70/1.84  Total                : 1.05
% 4.70/1.84  Index Insertion      : 0.00
% 4.70/1.84  Index Deletion       : 0.00
% 4.70/1.84  Index Matching       : 0.00
% 4.70/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
