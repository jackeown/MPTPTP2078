%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:37 EST 2020

% Result     : Theorem 5.55s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  159 (6261 expanded)
%              Number of leaves         :   49 (2200 expanded)
%              Depth                    :   19
%              Number of atoms          :  368 (17874 expanded)
%              Number of equality atoms :   74 (3836 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_161,axiom,(
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

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_157,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_77,axiom,(
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

tff(f_181,axiom,(
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

tff(c_74,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_78,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_86,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_78])).

tff(c_70,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_85,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_78])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_136,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_64])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_142,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_139])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_240,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_244,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_240])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_121,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_62])).

tff(c_245,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_121])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_108,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(u1_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_114,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_108])).

tff(c_118,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_114])).

tff(c_119,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_118])).

tff(c_254,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_119])).

tff(c_143,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_147,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_136,c_143])).

tff(c_216,plain,(
    ! [B_64,A_65] :
      ( k1_relat_1(B_64) = A_65
      | ~ v1_partfun1(B_64,A_65)
      | ~ v4_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_219,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_216])).

tff(c_222,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_219])).

tff(c_227,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_87,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66])).

tff(c_96,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_87])).

tff(c_255,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_96])).

tff(c_253,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_136])).

tff(c_334,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_partfun1(C_73,A_74)
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | v1_xboole_0(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_337,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_253,c_334])).

tff(c_340,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_255,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_227,c_340])).

tff(c_343,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_347,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_136])).

tff(c_34,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_392,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_347,c_34])).

tff(c_349,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_121])).

tff(c_404,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_349])).

tff(c_350,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_96])).

tff(c_412,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_350])).

tff(c_411,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_347])).

tff(c_2111,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( r2_funct_2(A_179,B_180,C_181,C_181)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(D_182,A_179,B_180)
      | ~ v1_funct_1(D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(C_181,A_179,B_180)
      | ~ v1_funct_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2115,plain,(
    ! [C_181] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_181,C_181)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_181,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_411,c_2111])).

tff(c_2271,plain,(
    ! [C_197] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_197,C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_197,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412,c_2115])).

tff(c_2276,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_411,c_2271])).

tff(c_2280,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412,c_2276])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_funct_1(k2_funct_1(A_14)) = A_14
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_410,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_392])).

tff(c_1747,plain,(
    ! [C_164,A_165,B_166] :
      ( v1_funct_1(k2_funct_1(C_164))
      | k2_relset_1(A_165,B_166,C_164) != B_166
      | ~ v2_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_funct_2(C_164,A_165,B_166)
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1750,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_411,c_1747])).

tff(c_1753,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412,c_60,c_410,c_1750])).

tff(c_1885,plain,(
    ! [C_168,B_169,A_170] :
      ( v1_funct_2(k2_funct_1(C_168),B_169,A_170)
      | k2_relset_1(A_170,B_169,C_168) != B_169
      | ~ v2_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169)))
      | ~ v1_funct_2(C_168,A_170,B_169)
      | ~ v1_funct_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1888,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_411,c_1885])).

tff(c_1891,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412,c_60,c_410,c_1888])).

tff(c_181,plain,(
    ! [A_63] :
      ( k4_relat_1(A_63) = k2_funct_1(A_63)
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_187,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_181])).

tff(c_193,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_187])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_200,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_6])).

tff(c_206,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_200])).

tff(c_1998,plain,(
    ! [C_174,B_175,A_176] :
      ( m1_subset_1(k2_funct_1(C_174),k1_zfmisc_1(k2_zfmisc_1(B_175,A_176)))
      | k2_relset_1(A_176,B_175,C_174) != B_175
      | ~ v2_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175)))
      | ~ v1_funct_2(C_174,A_176,B_175)
      | ~ v1_funct_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2201,plain,(
    ! [B_193,A_194,C_195] :
      ( k2_relset_1(B_193,A_194,k2_funct_1(C_195)) = k2_relat_1(k2_funct_1(C_195))
      | k2_relset_1(A_194,B_193,C_195) != B_193
      | ~ v2_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193)))
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ v1_funct_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_1998,c_34])).

tff(c_2207,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_411,c_2201])).

tff(c_2211,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412,c_60,c_410,c_206,c_2207])).

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

tff(c_197,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_8])).

tff(c_204,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_197])).

tff(c_40,plain,(
    ! [B_26] :
      ( v1_partfun1(B_26,k1_relat_1(B_26))
      | ~ v4_relat_1(B_26,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_211,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_40])).

tff(c_214,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_211])).

tff(c_480,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_483,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_480])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_483])).

tff(c_489,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_18,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_13] :
      ( k5_relat_1(k2_funct_1(A_13),A_13) = k6_relat_1(k2_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1720,plain,(
    ! [B_160,A_161] :
      ( v2_funct_1(B_160)
      | k2_relat_1(B_160) != k1_relat_1(A_161)
      | ~ v2_funct_1(k5_relat_1(B_160,A_161))
      | ~ v1_funct_1(B_160)
      | ~ v1_relat_1(B_160)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1723,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1720])).

tff(c_1728,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k2_relat_1(k2_funct_1(A_13)) != k1_relat_1(A_13)
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1723])).

tff(c_468,plain,(
    ! [A_81] :
      ( k5_relat_1(k2_funct_1(A_81),A_81) = k6_relat_1(k2_relat_1(A_81))
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1754,plain,(
    ! [A_167] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(A_167))) = k5_relat_1(A_167,k2_funct_1(A_167))
      | ~ v2_funct_1(k2_funct_1(A_167))
      | ~ v1_funct_1(k2_funct_1(A_167))
      | ~ v1_relat_1(k2_funct_1(A_167))
      | ~ v2_funct_1(A_167)
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_468])).

tff(c_1788,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_1754])).

tff(c_1801,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_60,c_489,c_1753,c_1788])).

tff(c_1802,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1801])).

tff(c_1805,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1728,c_1802])).

tff(c_1812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_60,c_489,c_1753,c_206,c_1805])).

tff(c_1814,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1801])).

tff(c_56,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_tops_2(A_36,B_37,C_38) = k2_funct_1(C_38)
      | ~ v2_funct_1(C_38)
      | k2_relset_1(A_36,B_37,C_38) != B_37
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3190,plain,(
    ! [B_224,A_225,C_226] :
      ( k2_tops_2(B_224,A_225,k2_funct_1(C_226)) = k2_funct_1(k2_funct_1(C_226))
      | ~ v2_funct_1(k2_funct_1(C_226))
      | k2_relset_1(B_224,A_225,k2_funct_1(C_226)) != A_225
      | ~ v1_funct_2(k2_funct_1(C_226),B_224,A_225)
      | ~ v1_funct_1(k2_funct_1(C_226))
      | k2_relset_1(A_225,B_224,C_226) != B_224
      | ~ v2_funct_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224)))
      | ~ v1_funct_2(C_226,A_225,B_224)
      | ~ v1_funct_1(C_226) ) ),
    inference(resolution,[status(thm)],[c_1998,c_56])).

tff(c_3196,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_411,c_3190])).

tff(c_3200,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412,c_60,c_410,c_1753,c_1891,c_2211,c_1814,c_3196])).

tff(c_1947,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_tops_2(A_171,B_172,C_173) = k2_funct_1(C_173)
      | ~ v2_funct_1(C_173)
      | k2_relset_1(A_171,B_172,C_173) != B_172
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(C_173,A_171,B_172)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1950,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_411,c_1947])).

tff(c_1953,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412,c_410,c_60,c_1950])).

tff(c_58,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_153,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_86,c_85,c_85,c_85,c_58])).

tff(c_345,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_343,c_343,c_153])).

tff(c_409,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_404,c_404,c_345])).

tff(c_1954,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_409])).

tff(c_3201,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3200,c_1954])).

tff(c_3208,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3201])).

tff(c_3211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_60,c_2280,c_3208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:57:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.55/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.10  
% 5.59/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.10  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.59/2.10  
% 5.59/2.10  %Foreground sorts:
% 5.59/2.10  
% 5.59/2.10  
% 5.59/2.10  %Background operators:
% 5.59/2.10  
% 5.59/2.10  
% 5.59/2.10  %Foreground operators:
% 5.59/2.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.59/2.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.59/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.59/2.10  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.59/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.59/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.59/2.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.59/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.59/2.10  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.59/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.59/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.59/2.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.59/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.59/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.59/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.59/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.59/2.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.59/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.59/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.59/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.59/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.59/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.59/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.59/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.59/2.10  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.59/2.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.59/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.59/2.10  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.59/2.10  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.59/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.59/2.10  
% 5.74/2.13  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.74/2.13  tff(f_203, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 5.74/2.13  tff(f_161, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.74/2.13  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.74/2.13  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.74/2.13  tff(f_169, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.74/2.13  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.74/2.13  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.74/2.13  tff(f_119, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.74/2.13  tff(f_141, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 5.74/2.13  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.74/2.13  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.74/2.13  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 5.74/2.13  tff(f_40, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 5.74/2.13  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.74/2.13  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.74/2.13  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.74/2.13  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 5.74/2.13  tff(f_181, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.74/2.13  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.74/2.13  tff(c_74, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_78, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.74/2.13  tff(c_86, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_78])).
% 5.74/2.13  tff(c_70, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_85, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_78])).
% 5.74/2.13  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_136, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_64])).
% 5.74/2.13  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.74/2.13  tff(c_139, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_136, c_2])).
% 5.74/2.13  tff(c_142, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_139])).
% 5.74/2.13  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_240, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.74/2.13  tff(c_244, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_240])).
% 5.74/2.13  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_121, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_62])).
% 5.74/2.13  tff(c_245, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_121])).
% 5.74/2.13  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_108, plain, (![A_51]: (~v1_xboole_0(u1_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.74/2.13  tff(c_114, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_108])).
% 5.74/2.13  tff(c_118, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_114])).
% 5.74/2.13  tff(c_119, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_118])).
% 5.74/2.13  tff(c_254, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_119])).
% 5.74/2.13  tff(c_143, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.74/2.13  tff(c_147, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_136, c_143])).
% 5.74/2.13  tff(c_216, plain, (![B_64, A_65]: (k1_relat_1(B_64)=A_65 | ~v1_partfun1(B_64, A_65) | ~v4_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.74/2.13  tff(c_219, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_147, c_216])).
% 5.74/2.13  tff(c_222, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_219])).
% 5.74/2.13  tff(c_227, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_222])).
% 5.74/2.13  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_87, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66])).
% 5.74/2.13  tff(c_96, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_87])).
% 5.74/2.13  tff(c_255, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_96])).
% 5.74/2.13  tff(c_253, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_136])).
% 5.74/2.13  tff(c_334, plain, (![C_73, A_74, B_75]: (v1_partfun1(C_73, A_74) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | v1_xboole_0(B_75))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.74/2.13  tff(c_337, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_253, c_334])).
% 5.74/2.13  tff(c_340, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_255, c_337])).
% 5.74/2.13  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_227, c_340])).
% 5.74/2.13  tff(c_343, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_222])).
% 5.74/2.13  tff(c_347, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_136])).
% 5.74/2.13  tff(c_34, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.74/2.13  tff(c_392, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_347, c_34])).
% 5.74/2.13  tff(c_349, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_121])).
% 5.74/2.13  tff(c_404, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_349])).
% 5.74/2.13  tff(c_350, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_96])).
% 5.74/2.13  tff(c_412, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_350])).
% 5.74/2.13  tff(c_411, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_347])).
% 5.74/2.13  tff(c_2111, plain, (![A_179, B_180, C_181, D_182]: (r2_funct_2(A_179, B_180, C_181, C_181) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(D_182, A_179, B_180) | ~v1_funct_1(D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(C_181, A_179, B_180) | ~v1_funct_1(C_181))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.74/2.13  tff(c_2115, plain, (![C_181]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_181, C_181) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_181, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_181))), inference(resolution, [status(thm)], [c_411, c_2111])).
% 5.74/2.13  tff(c_2271, plain, (![C_197]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_197, C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_197, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_197))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412, c_2115])).
% 5.74/2.13  tff(c_2276, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_411, c_2271])).
% 5.74/2.13  tff(c_2280, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412, c_2276])).
% 5.74/2.13  tff(c_28, plain, (![A_14]: (k2_funct_1(k2_funct_1(A_14))=A_14 | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.74/2.13  tff(c_410, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_392])).
% 5.74/2.13  tff(c_1747, plain, (![C_164, A_165, B_166]: (v1_funct_1(k2_funct_1(C_164)) | k2_relset_1(A_165, B_166, C_164)!=B_166 | ~v2_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_funct_2(C_164, A_165, B_166) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.74/2.13  tff(c_1750, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_411, c_1747])).
% 5.74/2.13  tff(c_1753, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412, c_60, c_410, c_1750])).
% 5.74/2.13  tff(c_1885, plain, (![C_168, B_169, A_170]: (v1_funct_2(k2_funct_1(C_168), B_169, A_170) | k2_relset_1(A_170, B_169, C_168)!=B_169 | ~v2_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))) | ~v1_funct_2(C_168, A_170, B_169) | ~v1_funct_1(C_168))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.74/2.13  tff(c_1888, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_411, c_1885])).
% 5.74/2.13  tff(c_1891, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412, c_60, c_410, c_1888])).
% 5.74/2.13  tff(c_181, plain, (![A_63]: (k4_relat_1(A_63)=k2_funct_1(A_63) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.74/2.13  tff(c_187, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_181])).
% 5.74/2.13  tff(c_193, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_187])).
% 5.74/2.13  tff(c_6, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.74/2.13  tff(c_200, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_193, c_6])).
% 5.74/2.13  tff(c_206, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_200])).
% 5.74/2.13  tff(c_1998, plain, (![C_174, B_175, A_176]: (m1_subset_1(k2_funct_1(C_174), k1_zfmisc_1(k2_zfmisc_1(B_175, A_176))) | k2_relset_1(A_176, B_175, C_174)!=B_175 | ~v2_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))) | ~v1_funct_2(C_174, A_176, B_175) | ~v1_funct_1(C_174))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.74/2.13  tff(c_2201, plain, (![B_193, A_194, C_195]: (k2_relset_1(B_193, A_194, k2_funct_1(C_195))=k2_relat_1(k2_funct_1(C_195)) | k2_relset_1(A_194, B_193, C_195)!=B_193 | ~v2_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))) | ~v1_funct_2(C_195, A_194, B_193) | ~v1_funct_1(C_195))), inference(resolution, [status(thm)], [c_1998, c_34])).
% 5.74/2.13  tff(c_2207, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_411, c_2201])).
% 5.74/2.13  tff(c_2211, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412, c_60, c_410, c_206, c_2207])).
% 5.74/2.13  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.74/2.13  tff(c_8, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.74/2.13  tff(c_197, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_193, c_8])).
% 5.74/2.13  tff(c_204, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_197])).
% 5.74/2.13  tff(c_40, plain, (![B_26]: (v1_partfun1(B_26, k1_relat_1(B_26)) | ~v4_relat_1(B_26, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.74/2.13  tff(c_211, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_40])).
% 5.74/2.13  tff(c_214, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_211])).
% 5.74/2.13  tff(c_480, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_214])).
% 5.74/2.13  tff(c_483, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_480])).
% 5.74/2.13  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_483])).
% 5.74/2.13  tff(c_489, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_214])).
% 5.74/2.13  tff(c_18, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.74/2.13  tff(c_24, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_relat_1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.74/2.13  tff(c_1720, plain, (![B_160, A_161]: (v2_funct_1(B_160) | k2_relat_1(B_160)!=k1_relat_1(A_161) | ~v2_funct_1(k5_relat_1(B_160, A_161)) | ~v1_funct_1(B_160) | ~v1_relat_1(B_160) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.74/2.13  tff(c_1723, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_13))) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1720])).
% 5.74/2.13  tff(c_1728, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1723])).
% 5.74/2.13  tff(c_468, plain, (![A_81]: (k5_relat_1(k2_funct_1(A_81), A_81)=k6_relat_1(k2_relat_1(A_81)) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.74/2.13  tff(c_1754, plain, (![A_167]: (k6_relat_1(k2_relat_1(k2_funct_1(A_167)))=k5_relat_1(A_167, k2_funct_1(A_167)) | ~v2_funct_1(k2_funct_1(A_167)) | ~v1_funct_1(k2_funct_1(A_167)) | ~v1_relat_1(k2_funct_1(A_167)) | ~v2_funct_1(A_167) | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(superposition, [status(thm), theory('equality')], [c_28, c_468])).
% 5.74/2.13  tff(c_1788, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_206, c_1754])).
% 5.74/2.13  tff(c_1801, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_60, c_489, c_1753, c_1788])).
% 5.74/2.13  tff(c_1802, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1801])).
% 5.74/2.13  tff(c_1805, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1728, c_1802])).
% 5.74/2.13  tff(c_1812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_60, c_489, c_1753, c_206, c_1805])).
% 5.74/2.13  tff(c_1814, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1801])).
% 5.74/2.13  tff(c_56, plain, (![A_36, B_37, C_38]: (k2_tops_2(A_36, B_37, C_38)=k2_funct_1(C_38) | ~v2_funct_1(C_38) | k2_relset_1(A_36, B_37, C_38)!=B_37 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(C_38, A_36, B_37) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.74/2.13  tff(c_3190, plain, (![B_224, A_225, C_226]: (k2_tops_2(B_224, A_225, k2_funct_1(C_226))=k2_funct_1(k2_funct_1(C_226)) | ~v2_funct_1(k2_funct_1(C_226)) | k2_relset_1(B_224, A_225, k2_funct_1(C_226))!=A_225 | ~v1_funct_2(k2_funct_1(C_226), B_224, A_225) | ~v1_funct_1(k2_funct_1(C_226)) | k2_relset_1(A_225, B_224, C_226)!=B_224 | ~v2_funct_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))) | ~v1_funct_2(C_226, A_225, B_224) | ~v1_funct_1(C_226))), inference(resolution, [status(thm)], [c_1998, c_56])).
% 5.74/2.13  tff(c_3196, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_411, c_3190])).
% 5.74/2.13  tff(c_3200, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412, c_60, c_410, c_1753, c_1891, c_2211, c_1814, c_3196])).
% 5.74/2.13  tff(c_1947, plain, (![A_171, B_172, C_173]: (k2_tops_2(A_171, B_172, C_173)=k2_funct_1(C_173) | ~v2_funct_1(C_173) | k2_relset_1(A_171, B_172, C_173)!=B_172 | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(C_173, A_171, B_172) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.74/2.13  tff(c_1950, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_411, c_1947])).
% 5.74/2.13  tff(c_1953, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412, c_410, c_60, c_1950])).
% 5.74/2.13  tff(c_58, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.74/2.13  tff(c_153, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_86, c_85, c_85, c_85, c_58])).
% 5.74/2.13  tff(c_345, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_343, c_343, c_153])).
% 5.74/2.13  tff(c_409, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_404, c_404, c_345])).
% 5.74/2.13  tff(c_1954, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_409])).
% 5.74/2.13  tff(c_3201, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3200, c_1954])).
% 5.74/2.13  tff(c_3208, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_3201])).
% 5.74/2.13  tff(c_3211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_60, c_2280, c_3208])).
% 5.74/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.13  
% 5.74/2.13  Inference rules
% 5.74/2.13  ----------------------
% 5.74/2.13  #Ref     : 0
% 5.74/2.13  #Sup     : 685
% 5.74/2.13  #Fact    : 0
% 5.74/2.13  #Define  : 0
% 5.74/2.13  #Split   : 22
% 5.74/2.13  #Chain   : 0
% 5.74/2.13  #Close   : 0
% 5.74/2.13  
% 5.74/2.13  Ordering : KBO
% 5.74/2.13  
% 5.74/2.13  Simplification rules
% 5.74/2.13  ----------------------
% 5.74/2.13  #Subsume      : 29
% 5.74/2.13  #Demod        : 1631
% 5.74/2.13  #Tautology    : 394
% 5.74/2.13  #SimpNegUnit  : 7
% 5.74/2.13  #BackRed      : 51
% 5.74/2.13  
% 5.74/2.13  #Partial instantiations: 0
% 5.74/2.13  #Strategies tried      : 1
% 5.74/2.13  
% 5.74/2.13  Timing (in seconds)
% 5.74/2.13  ----------------------
% 5.74/2.13  Preprocessing        : 0.39
% 5.74/2.13  Parsing              : 0.21
% 5.74/2.13  CNF conversion       : 0.03
% 5.74/2.13  Main loop            : 0.90
% 5.74/2.13  Inferencing          : 0.30
% 5.74/2.13  Reduction            : 0.34
% 5.74/2.13  Demodulation         : 0.26
% 5.74/2.13  BG Simplification    : 0.04
% 5.74/2.13  Subsumption          : 0.15
% 5.74/2.13  Abstraction          : 0.04
% 5.74/2.13  MUC search           : 0.00
% 5.74/2.13  Cooper               : 0.00
% 5.74/2.13  Total                : 1.34
% 5.74/2.13  Index Insertion      : 0.00
% 5.74/2.13  Index Deletion       : 0.00
% 5.74/2.13  Index Matching       : 0.00
% 5.74/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
