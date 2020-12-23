%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:38 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :  184 (43037 expanded)
%              Number of leaves         :   47 (14940 expanded)
%              Depth                    :   30
%              Number of atoms          :  539 (123484 expanded)
%              Number of equality atoms :  119 (26738 expanded)
%              Maximal formula depth    :   13 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_166,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_146,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_186,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
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

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_83,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_76])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_116,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_62])).

tff(c_164,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_168,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_164])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_110,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_60])).

tff(c_178,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_110])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_97,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(u1_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_103,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_97])).

tff(c_107,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_103])).

tff(c_108,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_107])).

tff(c_187,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_108])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_122,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_128,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_132,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_116,c_128])).

tff(c_156,plain,(
    ! [B_63,A_64] :
      ( k1_relat_1(B_63) = A_64
      | ~ v1_partfun1(B_63,A_64)
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_159,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_156])).

tff(c_162,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_159])).

tff(c_163,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_85,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_64])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_85])).

tff(c_188,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_94])).

tff(c_186,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_116])).

tff(c_238,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_partfun1(C_70,A_71)
      | ~ v1_funct_2(C_70,A_71,B_72)
      | ~ v1_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | v1_xboole_0(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_241,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_186,c_238])).

tff(c_244,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_188,c_241])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_163,c_244])).

tff(c_247,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_251,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_116])).

tff(c_32,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_301,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_251,c_32])).

tff(c_252,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_110])).

tff(c_309,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_252])).

tff(c_254,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_94])).

tff(c_316,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_254])).

tff(c_315,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_251])).

tff(c_488,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( r2_funct_2(A_103,B_104,C_105,C_105)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_2(D_106,A_103,B_104)
      | ~ v1_funct_1(D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_2(C_105,A_103,B_104)
      | ~ v1_funct_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_492,plain,(
    ! [C_105] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_105,C_105)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_105,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_315,c_488])).

tff(c_574,plain,(
    ! [C_116] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_116,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_116,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_492])).

tff(c_579,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_574])).

tff(c_583,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_579])).

tff(c_314,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_301])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_430,plain,(
    ! [C_93,B_94,A_95] :
      ( v1_funct_2(k2_funct_1(C_93),B_94,A_95)
      | k2_relset_1(A_95,B_94,C_93) != B_94
      | ~ v2_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94)))
      | ~ v1_funct_2(C_93,A_95,B_94)
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_433,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_430])).

tff(c_436,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_58,c_314,c_433])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_453,plain,(
    ! [C_100,B_101,A_102] :
      ( m1_subset_1(k2_funct_1(C_100),k1_zfmisc_1(k2_zfmisc_1(B_101,A_102)))
      | k2_relset_1(A_102,B_101,C_100) != B_101
      | ~ v2_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2(C_100,A_102,B_101)
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_477,plain,(
    ! [C_100,B_101,A_102] :
      ( v1_relat_1(k2_funct_1(C_100))
      | ~ v1_relat_1(k2_zfmisc_1(B_101,A_102))
      | k2_relset_1(A_102,B_101,C_100) != B_101
      | ~ v2_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2(C_100,A_102,B_101)
      | ~ v1_funct_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_453,c_2])).

tff(c_497,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(k2_funct_1(C_107))
      | k2_relset_1(A_108,B_109,C_107) != B_109
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_477])).

tff(c_503,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_497])).

tff(c_507,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_58,c_314,c_503])).

tff(c_414,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_funct_1(k2_funct_1(C_88))
      | k2_relset_1(A_89,B_90,C_88) != B_90
      | ~ v2_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_2(C_88,A_89,B_90)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_417,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_414])).

tff(c_420,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_58,c_314,c_417])).

tff(c_30,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_519,plain,(
    ! [C_113,B_114,A_115] :
      ( v4_relat_1(k2_funct_1(C_113),B_114)
      | k2_relset_1(A_115,B_114,C_113) != B_114
      | ~ v2_funct_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_2(C_113,A_115,B_114)
      | ~ v1_funct_1(C_113) ) ),
    inference(resolution,[status(thm)],[c_453,c_30])).

tff(c_525,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_519])).

tff(c_529,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_58,c_314,c_525])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_134,plain,(
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

tff(c_408,plain,(
    ! [A_85] :
      ( v1_partfun1(k2_funct_1(A_85),k1_relat_1(k2_funct_1(A_85)))
      | ~ v4_relat_1(k2_funct_1(A_85),k2_relat_1(A_85))
      | ~ v1_relat_1(k2_funct_1(A_85))
      | ~ v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_38])).

tff(c_411,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_20,c_408])).

tff(c_532,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_529,c_411])).

tff(c_538,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66,c_58,c_507,c_532])).

tff(c_40,plain,(
    ! [B_27,A_26] :
      ( k1_relat_1(B_27) = A_26
      | ~ v1_partfun1(B_27,A_26)
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_535,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_529,c_40])).

tff(c_541,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_535])).

tff(c_543,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_541])).

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

tff(c_386,plain,(
    ! [A_81,B_82] :
      ( v2_funct_1(A_81)
      | k2_relat_1(B_82) != k1_relat_1(A_81)
      | ~ v2_funct_1(k5_relat_1(B_82,A_81))
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_392,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_24,c_386])).

tff(c_396,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k1_relat_1(k2_funct_1(A_12)) != k2_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_392])).

tff(c_26,plain,(
    ! [A_13,B_15] :
      ( k2_funct_1(A_13) = B_15
      | k6_relat_1(k1_relat_1(A_13)) != k5_relat_1(A_13,B_15)
      | k2_relat_1(A_13) != k1_relat_1(B_15)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_546,plain,(
    ! [B_15] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_15
      | k5_relat_1(k2_funct_1('#skF_3'),B_15) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_15)
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_26])).

tff(c_562,plain,(
    ! [B_15] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_15
      | k5_relat_1(k2_funct_1('#skF_3'),B_15) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_15)
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_420,c_546])).

tff(c_599,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_562])).

tff(c_606,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_396,c_599])).

tff(c_613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66,c_58,c_507,c_420,c_543,c_606])).

tff(c_616,plain,(
    ! [B_121] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_121
      | k5_relat_1(k2_funct_1('#skF_3'),B_121) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_121)
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(splitRight,[status(thm)],[c_562])).

tff(c_620,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_616])).

tff(c_627,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66,c_58,c_620])).

tff(c_631,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_634,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_631])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66,c_58,c_634])).

tff(c_640,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_584,plain,(
    ! [B_117,A_118,C_119] :
      ( k2_relset_1(B_117,A_118,k2_funct_1(C_119)) = k2_relat_1(k2_funct_1(C_119))
      | k2_relset_1(A_118,B_117,C_119) != B_117
      | ~ v2_funct_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ v1_funct_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_453,c_32])).

tff(c_590,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_584])).

tff(c_594,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_58,c_314,c_590])).

tff(c_718,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_594])).

tff(c_615,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_562])).

tff(c_639,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_6,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_397,plain,(
    ! [B_83,A_84] :
      ( v2_funct_1(B_83)
      | k2_relat_1(B_83) != k1_relat_1(A_84)
      | ~ v2_funct_1(k5_relat_1(B_83,A_84))
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_400,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k2_relat_1(k2_funct_1(A_12)) != k1_relat_1(A_12)
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_12)))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_397])).

tff(c_405,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k2_relat_1(k2_funct_1(A_12)) != k1_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_400])).

tff(c_421,plain,(
    ! [A_91,B_92] :
      ( k2_funct_1(A_91) = B_92
      | k6_relat_1(k1_relat_1(A_91)) != k5_relat_1(A_91,B_92)
      | k2_relat_1(A_91) != k1_relat_1(B_92)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_837,plain,(
    ! [A_128] :
      ( k2_funct_1(k2_funct_1(A_128)) = A_128
      | k6_relat_1(k1_relat_1(k2_funct_1(A_128))) != k6_relat_1(k2_relat_1(A_128))
      | k2_relat_1(k2_funct_1(A_128)) != k1_relat_1(A_128)
      | ~ v2_funct_1(k2_funct_1(A_128))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128)
      | ~ v1_funct_1(k2_funct_1(A_128))
      | ~ v1_relat_1(k2_funct_1(A_128))
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_421])).

tff(c_853,plain,(
    ! [A_129] :
      ( k2_funct_1(k2_funct_1(A_129)) = A_129
      | k2_relat_1(k2_funct_1(A_129)) != k1_relat_1(A_129)
      | ~ v2_funct_1(k2_funct_1(A_129))
      | ~ v1_funct_1(k2_funct_1(A_129))
      | ~ v1_relat_1(k2_funct_1(A_129))
      | ~ v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_837])).

tff(c_873,plain,(
    ! [A_130] :
      ( k2_funct_1(k2_funct_1(A_130)) = A_130
      | k2_relat_1(k2_funct_1(A_130)) != k1_relat_1(A_130)
      | ~ v1_funct_1(k2_funct_1(A_130))
      | ~ v1_relat_1(k2_funct_1(A_130))
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_405,c_853])).

tff(c_889,plain,(
    ! [A_131] :
      ( k2_funct_1(k2_funct_1(A_131)) = A_131
      | k2_relat_1(k2_funct_1(A_131)) != k1_relat_1(A_131)
      | ~ v1_funct_1(k2_funct_1(A_131))
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(resolution,[status(thm)],[c_8,c_873])).

tff(c_916,plain,(
    ! [A_133] :
      ( k2_funct_1(k2_funct_1(A_133)) = A_133
      | k2_relat_1(k2_funct_1(A_133)) != k1_relat_1(A_133)
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_889])).

tff(c_932,plain,(
    ! [A_134] :
      ( k2_funct_1(k2_funct_1(A_134)) = A_134
      | ~ v2_funct_1(A_134)
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_916])).

tff(c_44,plain,(
    ! [C_34,B_33,A_32] :
      ( m1_subset_1(k2_funct_1(C_34),k1_zfmisc_1(k2_zfmisc_1(B_33,A_32)))
      | k2_relset_1(A_32,B_33,C_34) != B_33
      | ~ v2_funct_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1451,plain,(
    ! [A_153,B_154,A_155] :
      ( m1_subset_1(A_153,k1_zfmisc_1(k2_zfmisc_1(B_154,A_155)))
      | k2_relset_1(A_155,B_154,k2_funct_1(A_153)) != B_154
      | ~ v2_funct_1(k2_funct_1(A_153))
      | ~ m1_subset_1(k2_funct_1(A_153),k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_2(k2_funct_1(A_153),A_155,B_154)
      | ~ v1_funct_1(k2_funct_1(A_153))
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_44])).

tff(c_1457,plain,(
    ! [B_154,A_155] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_154,A_155)))
      | k2_relset_1(A_155,B_154,k2_funct_1(k2_funct_1('#skF_3'))) != B_154
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_155,B_154)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_1451])).

tff(c_1464,plain,(
    ! [B_156,A_157] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_156,A_157)))
      | k2_relset_1(A_157,B_156,'#skF_3') != B_156
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_2('#skF_3',A_157,B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_420,c_615,c_66,c_639,c_639,c_58,c_639,c_639,c_1457])).

tff(c_54,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_tops_2(A_37,B_38,C_39) = k2_funct_1(C_39)
      | ~ v2_funct_1(C_39)
      | k2_relset_1(A_37,B_38,C_39) != B_38
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1502,plain,(
    ! [B_156,A_157] :
      ( k2_tops_2(B_156,A_157,k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(B_156,A_157,k2_funct_1('#skF_3')) != A_157
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_156,A_157)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(A_157,B_156,'#skF_3') != B_156
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_2('#skF_3',A_157,B_156) ) ),
    inference(resolution,[status(thm)],[c_1464,c_54])).

tff(c_1632,plain,(
    ! [B_171,A_172] :
      ( k2_tops_2(B_171,A_172,k2_funct_1('#skF_3')) = '#skF_3'
      | k2_relset_1(B_171,A_172,k2_funct_1('#skF_3')) != A_172
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_171,A_172)
      | k2_relset_1(A_172,B_171,'#skF_3') != B_171
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_172,B_171)))
      | ~ v1_funct_2('#skF_3',A_172,B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_615,c_639,c_1502])).

tff(c_1635,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_315,c_1632])).

tff(c_1638,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_314,c_436,c_718,c_1635])).

tff(c_437,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_tops_2(A_96,B_97,C_98) = k2_funct_1(C_98)
      | ~ v2_funct_1(C_98)
      | k2_relset_1(A_96,B_97,C_98) != B_97
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_440,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_437])).

tff(c_443,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_316,c_314,c_58,c_440])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_146,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_84,c_83,c_83,c_83,c_56])).

tff(c_249,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_247,c_247,c_146])).

tff(c_385,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_309,c_249])).

tff(c_444,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_385])).

tff(c_1639,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1638,c_444])).

tff(c_1642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_1639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.83  
% 5.11/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.83  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.11/1.83  
% 5.11/1.83  %Foreground sorts:
% 5.11/1.83  
% 5.11/1.83  
% 5.11/1.83  %Background operators:
% 5.11/1.83  
% 5.11/1.83  
% 5.11/1.83  %Foreground operators:
% 5.11/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.11/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.11/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.11/1.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.11/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.11/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.11/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.11/1.83  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.11/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.11/1.83  tff('#skF_2', type, '#skF_2': $i).
% 5.11/1.83  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.11/1.83  tff('#skF_3', type, '#skF_3': $i).
% 5.11/1.83  tff('#skF_1', type, '#skF_1': $i).
% 5.11/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.11/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.11/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.11/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.11/1.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.11/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.11/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.11/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.11/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.11/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.11/1.83  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.11/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.11/1.83  
% 5.16/1.86  tff(f_208, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 5.16/1.86  tff(f_166, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.16/1.86  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.16/1.86  tff(f_174, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.16/1.86  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.16/1.86  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.16/1.86  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.16/1.86  tff(f_132, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.16/1.86  tff(f_124, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.16/1.86  tff(f_146, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 5.16/1.86  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.16/1.86  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.16/1.86  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.16/1.86  tff(f_46, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.16/1.86  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 5.16/1.86  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.16/1.86  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.16/1.86  tff(f_186, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.16/1.86  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_72, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_76, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.16/1.86  tff(c_84, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_76])).
% 5.16/1.86  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_83, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_76])).
% 5.16/1.86  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_116, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_62])).
% 5.16/1.86  tff(c_164, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.16/1.86  tff(c_168, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_116, c_164])).
% 5.16/1.86  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_110, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_60])).
% 5.16/1.86  tff(c_178, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_110])).
% 5.16/1.86  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_97, plain, (![A_51]: (~v1_xboole_0(u1_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.16/1.86  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83, c_97])).
% 5.16/1.86  tff(c_107, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_103])).
% 5.16/1.86  tff(c_108, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_107])).
% 5.16/1.86  tff(c_187, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_108])).
% 5.16/1.86  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.16/1.86  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.16/1.86  tff(c_119, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_116, c_2])).
% 5.16/1.86  tff(c_122, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_119])).
% 5.16/1.86  tff(c_128, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.16/1.86  tff(c_132, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_116, c_128])).
% 5.16/1.86  tff(c_156, plain, (![B_63, A_64]: (k1_relat_1(B_63)=A_64 | ~v1_partfun1(B_63, A_64) | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/1.86  tff(c_159, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_156])).
% 5.16/1.86  tff(c_162, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_159])).
% 5.16/1.86  tff(c_163, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_162])).
% 5.16/1.86  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_85, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_64])).
% 5.16/1.86  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_85])).
% 5.16/1.86  tff(c_188, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_94])).
% 5.16/1.86  tff(c_186, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_116])).
% 5.16/1.86  tff(c_238, plain, (![C_70, A_71, B_72]: (v1_partfun1(C_70, A_71) | ~v1_funct_2(C_70, A_71, B_72) | ~v1_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | v1_xboole_0(B_72))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.16/1.86  tff(c_241, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_186, c_238])).
% 5.16/1.86  tff(c_244, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_188, c_241])).
% 5.16/1.86  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_163, c_244])).
% 5.16/1.86  tff(c_247, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_162])).
% 5.16/1.86  tff(c_251, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_116])).
% 5.16/1.86  tff(c_32, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.16/1.86  tff(c_301, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_251, c_32])).
% 5.16/1.86  tff(c_252, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_110])).
% 5.16/1.86  tff(c_309, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_252])).
% 5.16/1.86  tff(c_254, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_94])).
% 5.16/1.86  tff(c_316, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_254])).
% 5.16/1.86  tff(c_315, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_251])).
% 5.16/1.86  tff(c_488, plain, (![A_103, B_104, C_105, D_106]: (r2_funct_2(A_103, B_104, C_105, C_105) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_2(D_106, A_103, B_104) | ~v1_funct_1(D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_2(C_105, A_103, B_104) | ~v1_funct_1(C_105))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.16/1.86  tff(c_492, plain, (![C_105]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_105, C_105) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_105, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_105))), inference(resolution, [status(thm)], [c_315, c_488])).
% 5.16/1.86  tff(c_574, plain, (![C_116]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_116, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_116, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_116))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_492])).
% 5.16/1.86  tff(c_579, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_574])).
% 5.16/1.86  tff(c_583, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_579])).
% 5.16/1.86  tff(c_314, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_301])).
% 5.16/1.86  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_430, plain, (![C_93, B_94, A_95]: (v1_funct_2(k2_funct_1(C_93), B_94, A_95) | k2_relset_1(A_95, B_94, C_93)!=B_94 | ~v2_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))) | ~v1_funct_2(C_93, A_95, B_94) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.16/1.86  tff(c_433, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_430])).
% 5.16/1.86  tff(c_436, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_58, c_314, c_433])).
% 5.16/1.86  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.16/1.86  tff(c_22, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.16/1.86  tff(c_453, plain, (![C_100, B_101, A_102]: (m1_subset_1(k2_funct_1(C_100), k1_zfmisc_1(k2_zfmisc_1(B_101, A_102))) | k2_relset_1(A_102, B_101, C_100)!=B_101 | ~v2_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2(C_100, A_102, B_101) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.16/1.86  tff(c_477, plain, (![C_100, B_101, A_102]: (v1_relat_1(k2_funct_1(C_100)) | ~v1_relat_1(k2_zfmisc_1(B_101, A_102)) | k2_relset_1(A_102, B_101, C_100)!=B_101 | ~v2_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2(C_100, A_102, B_101) | ~v1_funct_1(C_100))), inference(resolution, [status(thm)], [c_453, c_2])).
% 5.16/1.86  tff(c_497, plain, (![C_107, A_108, B_109]: (v1_relat_1(k2_funct_1(C_107)) | k2_relset_1(A_108, B_109, C_107)!=B_109 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_477])).
% 5.16/1.86  tff(c_503, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_497])).
% 5.16/1.86  tff(c_507, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_58, c_314, c_503])).
% 5.16/1.86  tff(c_414, plain, (![C_88, A_89, B_90]: (v1_funct_1(k2_funct_1(C_88)) | k2_relset_1(A_89, B_90, C_88)!=B_90 | ~v2_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_2(C_88, A_89, B_90) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.16/1.86  tff(c_417, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_414])).
% 5.16/1.86  tff(c_420, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_58, c_314, c_417])).
% 5.16/1.86  tff(c_30, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.16/1.86  tff(c_519, plain, (![C_113, B_114, A_115]: (v4_relat_1(k2_funct_1(C_113), B_114) | k2_relset_1(A_115, B_114, C_113)!=B_114 | ~v2_funct_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_2(C_113, A_115, B_114) | ~v1_funct_1(C_113))), inference(resolution, [status(thm)], [c_453, c_30])).
% 5.16/1.86  tff(c_525, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_519])).
% 5.16/1.86  tff(c_529, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_58, c_314, c_525])).
% 5.16/1.86  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.16/1.86  tff(c_134, plain, (![A_61]: (k1_relat_1(k2_funct_1(A_61))=k2_relat_1(A_61) | ~v2_funct_1(A_61) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.16/1.86  tff(c_38, plain, (![B_27]: (v1_partfun1(B_27, k1_relat_1(B_27)) | ~v4_relat_1(B_27, k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/1.86  tff(c_408, plain, (![A_85]: (v1_partfun1(k2_funct_1(A_85), k1_relat_1(k2_funct_1(A_85))) | ~v4_relat_1(k2_funct_1(A_85), k2_relat_1(A_85)) | ~v1_relat_1(k2_funct_1(A_85)) | ~v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_134, c_38])).
% 5.16/1.86  tff(c_411, plain, (![A_11]: (v1_partfun1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v4_relat_1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_408])).
% 5.16/1.86  tff(c_532, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_529, c_411])).
% 5.16/1.86  tff(c_538, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_66, c_58, c_507, c_532])).
% 5.16/1.86  tff(c_40, plain, (![B_27, A_26]: (k1_relat_1(B_27)=A_26 | ~v1_partfun1(B_27, A_26) | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/1.86  tff(c_535, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_529, c_40])).
% 5.16/1.86  tff(c_541, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_535])).
% 5.16/1.86  tff(c_543, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_541])).
% 5.16/1.86  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.16/1.86  tff(c_24, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.16/1.86  tff(c_386, plain, (![A_81, B_82]: (v2_funct_1(A_81) | k2_relat_1(B_82)!=k1_relat_1(A_81) | ~v2_funct_1(k5_relat_1(B_82, A_81)) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.16/1.86  tff(c_392, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_12))) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_386])).
% 5.16/1.86  tff(c_396, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_392])).
% 5.16/1.86  tff(c_26, plain, (![A_13, B_15]: (k2_funct_1(A_13)=B_15 | k6_relat_1(k1_relat_1(A_13))!=k5_relat_1(A_13, B_15) | k2_relat_1(A_13)!=k1_relat_1(B_15) | ~v2_funct_1(A_13) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.16/1.86  tff(c_546, plain, (![B_15]: (k2_funct_1(k2_funct_1('#skF_3'))=B_15 | k5_relat_1(k2_funct_1('#skF_3'), B_15)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_15) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_543, c_26])).
% 5.16/1.86  tff(c_562, plain, (![B_15]: (k2_funct_1(k2_funct_1('#skF_3'))=B_15 | k5_relat_1(k2_funct_1('#skF_3'), B_15)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_15) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_420, c_546])).
% 5.16/1.86  tff(c_599, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_562])).
% 5.16/1.86  tff(c_606, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_396, c_599])).
% 5.16/1.86  tff(c_613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_66, c_58, c_507, c_420, c_543, c_606])).
% 5.16/1.86  tff(c_616, plain, (![B_121]: (k2_funct_1(k2_funct_1('#skF_3'))=B_121 | k5_relat_1(k2_funct_1('#skF_3'), B_121)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_121) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(splitRight, [status(thm)], [c_562])).
% 5.16/1.86  tff(c_620, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_616])).
% 5.16/1.86  tff(c_627, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_66, c_58, c_620])).
% 5.16/1.86  tff(c_631, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_627])).
% 5.16/1.86  tff(c_634, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_631])).
% 5.16/1.86  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_66, c_58, c_634])).
% 5.16/1.86  tff(c_640, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_627])).
% 5.16/1.86  tff(c_584, plain, (![B_117, A_118, C_119]: (k2_relset_1(B_117, A_118, k2_funct_1(C_119))=k2_relat_1(k2_funct_1(C_119)) | k2_relset_1(A_118, B_117, C_119)!=B_117 | ~v2_funct_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_2(C_119, A_118, B_117) | ~v1_funct_1(C_119))), inference(resolution, [status(thm)], [c_453, c_32])).
% 5.16/1.86  tff(c_590, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_584])).
% 5.16/1.86  tff(c_594, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_58, c_314, c_590])).
% 5.16/1.86  tff(c_718, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_640, c_594])).
% 5.16/1.86  tff(c_615, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_562])).
% 5.16/1.86  tff(c_639, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_627])).
% 5.16/1.86  tff(c_6, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.16/1.86  tff(c_8, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.16/1.86  tff(c_397, plain, (![B_83, A_84]: (v2_funct_1(B_83) | k2_relat_1(B_83)!=k1_relat_1(A_84) | ~v2_funct_1(k5_relat_1(B_83, A_84)) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.16/1.86  tff(c_400, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k2_relat_1(k2_funct_1(A_12))!=k1_relat_1(A_12) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_12))) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_22, c_397])).
% 5.16/1.86  tff(c_405, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k2_relat_1(k2_funct_1(A_12))!=k1_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_400])).
% 5.16/1.86  tff(c_421, plain, (![A_91, B_92]: (k2_funct_1(A_91)=B_92 | k6_relat_1(k1_relat_1(A_91))!=k5_relat_1(A_91, B_92) | k2_relat_1(A_91)!=k1_relat_1(B_92) | ~v2_funct_1(A_91) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.16/1.86  tff(c_837, plain, (![A_128]: (k2_funct_1(k2_funct_1(A_128))=A_128 | k6_relat_1(k1_relat_1(k2_funct_1(A_128)))!=k6_relat_1(k2_relat_1(A_128)) | k2_relat_1(k2_funct_1(A_128))!=k1_relat_1(A_128) | ~v2_funct_1(k2_funct_1(A_128)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128) | ~v1_funct_1(k2_funct_1(A_128)) | ~v1_relat_1(k2_funct_1(A_128)) | ~v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(superposition, [status(thm), theory('equality')], [c_22, c_421])).
% 5.16/1.86  tff(c_853, plain, (![A_129]: (k2_funct_1(k2_funct_1(A_129))=A_129 | k2_relat_1(k2_funct_1(A_129))!=k1_relat_1(A_129) | ~v2_funct_1(k2_funct_1(A_129)) | ~v1_funct_1(k2_funct_1(A_129)) | ~v1_relat_1(k2_funct_1(A_129)) | ~v2_funct_1(A_129) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(superposition, [status(thm), theory('equality')], [c_20, c_837])).
% 5.16/1.86  tff(c_873, plain, (![A_130]: (k2_funct_1(k2_funct_1(A_130))=A_130 | k2_relat_1(k2_funct_1(A_130))!=k1_relat_1(A_130) | ~v1_funct_1(k2_funct_1(A_130)) | ~v1_relat_1(k2_funct_1(A_130)) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_405, c_853])).
% 5.16/1.86  tff(c_889, plain, (![A_131]: (k2_funct_1(k2_funct_1(A_131))=A_131 | k2_relat_1(k2_funct_1(A_131))!=k1_relat_1(A_131) | ~v1_funct_1(k2_funct_1(A_131)) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(resolution, [status(thm)], [c_8, c_873])).
% 5.16/1.86  tff(c_916, plain, (![A_133]: (k2_funct_1(k2_funct_1(A_133))=A_133 | k2_relat_1(k2_funct_1(A_133))!=k1_relat_1(A_133) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(resolution, [status(thm)], [c_6, c_889])).
% 5.16/1.86  tff(c_932, plain, (![A_134]: (k2_funct_1(k2_funct_1(A_134))=A_134 | ~v2_funct_1(A_134) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_18, c_916])).
% 5.16/1.86  tff(c_44, plain, (![C_34, B_33, A_32]: (m1_subset_1(k2_funct_1(C_34), k1_zfmisc_1(k2_zfmisc_1(B_33, A_32))) | k2_relset_1(A_32, B_33, C_34)!=B_33 | ~v2_funct_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.16/1.86  tff(c_1451, plain, (![A_153, B_154, A_155]: (m1_subset_1(A_153, k1_zfmisc_1(k2_zfmisc_1(B_154, A_155))) | k2_relset_1(A_155, B_154, k2_funct_1(A_153))!=B_154 | ~v2_funct_1(k2_funct_1(A_153)) | ~m1_subset_1(k2_funct_1(A_153), k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_2(k2_funct_1(A_153), A_155, B_154) | ~v1_funct_1(k2_funct_1(A_153)) | ~v2_funct_1(A_153) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_932, c_44])).
% 5.16/1.86  tff(c_1457, plain, (![B_154, A_155]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_154, A_155))) | k2_relset_1(A_155, B_154, k2_funct_1(k2_funct_1('#skF_3')))!=B_154 | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_155, B_154) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_639, c_1451])).
% 5.16/1.86  tff(c_1464, plain, (![B_156, A_157]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_156, A_157))) | k2_relset_1(A_157, B_156, '#skF_3')!=B_156 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_2('#skF_3', A_157, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_420, c_615, c_66, c_639, c_639, c_58, c_639, c_639, c_1457])).
% 5.16/1.86  tff(c_54, plain, (![A_37, B_38, C_39]: (k2_tops_2(A_37, B_38, C_39)=k2_funct_1(C_39) | ~v2_funct_1(C_39) | k2_relset_1(A_37, B_38, C_39)!=B_38 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(C_39, A_37, B_38) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.16/1.86  tff(c_1502, plain, (![B_156, A_157]: (k2_tops_2(B_156, A_157, k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(B_156, A_157, k2_funct_1('#skF_3'))!=A_157 | ~v1_funct_2(k2_funct_1('#skF_3'), B_156, A_157) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(A_157, B_156, '#skF_3')!=B_156 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_2('#skF_3', A_157, B_156))), inference(resolution, [status(thm)], [c_1464, c_54])).
% 5.16/1.86  tff(c_1632, plain, (![B_171, A_172]: (k2_tops_2(B_171, A_172, k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(B_171, A_172, k2_funct_1('#skF_3'))!=A_172 | ~v1_funct_2(k2_funct_1('#skF_3'), B_171, A_172) | k2_relset_1(A_172, B_171, '#skF_3')!=B_171 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))) | ~v1_funct_2('#skF_3', A_172, B_171))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_615, c_639, c_1502])).
% 5.16/1.86  tff(c_1635, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_315, c_1632])).
% 5.16/1.86  tff(c_1638, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_316, c_314, c_436, c_718, c_1635])).
% 5.16/1.86  tff(c_437, plain, (![A_96, B_97, C_98]: (k2_tops_2(A_96, B_97, C_98)=k2_funct_1(C_98) | ~v2_funct_1(C_98) | k2_relset_1(A_96, B_97, C_98)!=B_97 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.16/1.86  tff(c_440, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_437])).
% 5.16/1.86  tff(c_443, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_316, c_314, c_58, c_440])).
% 5.16/1.86  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.16/1.86  tff(c_146, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84, c_84, c_83, c_83, c_83, c_56])).
% 5.16/1.86  tff(c_249, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_247, c_247, c_146])).
% 5.16/1.86  tff(c_385, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_309, c_249])).
% 5.16/1.86  tff(c_444, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_385])).
% 5.16/1.86  tff(c_1639, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1638, c_444])).
% 5.16/1.86  tff(c_1642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_583, c_1639])).
% 5.16/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.86  
% 5.16/1.86  Inference rules
% 5.16/1.86  ----------------------
% 5.16/1.86  #Ref     : 0
% 5.16/1.86  #Sup     : 341
% 5.16/1.86  #Fact    : 0
% 5.16/1.86  #Define  : 0
% 5.16/1.86  #Split   : 5
% 5.16/1.86  #Chain   : 0
% 5.16/1.86  #Close   : 0
% 5.16/1.86  
% 5.16/1.86  Ordering : KBO
% 5.16/1.86  
% 5.16/1.86  Simplification rules
% 5.16/1.86  ----------------------
% 5.16/1.86  #Subsume      : 34
% 5.16/1.86  #Demod        : 913
% 5.16/1.86  #Tautology    : 209
% 5.16/1.86  #SimpNegUnit  : 8
% 5.16/1.86  #BackRed      : 27
% 5.16/1.86  
% 5.16/1.86  #Partial instantiations: 0
% 5.16/1.86  #Strategies tried      : 1
% 5.16/1.86  
% 5.16/1.86  Timing (in seconds)
% 5.16/1.86  ----------------------
% 5.16/1.87  Preprocessing        : 0.40
% 5.16/1.87  Parsing              : 0.22
% 5.16/1.87  CNF conversion       : 0.03
% 5.16/1.87  Main loop            : 0.66
% 5.16/1.87  Inferencing          : 0.23
% 5.16/1.87  Reduction            : 0.24
% 5.16/1.87  Demodulation         : 0.18
% 5.16/1.87  BG Simplification    : 0.05
% 5.16/1.87  Subsumption          : 0.11
% 5.16/1.87  Abstraction          : 0.04
% 5.16/1.87  MUC search           : 0.00
% 5.16/1.87  Cooper               : 0.00
% 5.16/1.87  Total                : 1.13
% 5.16/1.87  Index Insertion      : 0.00
% 5.16/1.87  Index Deletion       : 0.00
% 5.16/1.87  Index Matching       : 0.00
% 5.16/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
