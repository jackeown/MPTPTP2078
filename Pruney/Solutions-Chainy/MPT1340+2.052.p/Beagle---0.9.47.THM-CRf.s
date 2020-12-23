%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:37 EST 2020

% Result     : Theorem 6.85s
% Output     : CNFRefutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :  154 (3713 expanded)
%              Number of leaves         :   49 (1330 expanded)
%              Depth                    :   17
%              Number of atoms          :  363 (10790 expanded)
%              Number of equality atoms :   72 (2383 expanded)
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
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

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

tff(c_124,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_64])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_216,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_220,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_216])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_119,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_62])).

tff(c_221,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_119])).

tff(c_54,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k2_struct_0(A_35))
      | ~ l1_struct_0(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_235,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_54])).

tff(c_239,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_235])).

tff(c_240,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_239])).

tff(c_136,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_140,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_124,c_136])).

tff(c_209,plain,(
    ! [B_65,A_66] :
      ( k1_relat_1(B_65) = A_66
      | ~ v1_partfun1(B_65,A_66)
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_212,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_209])).

tff(c_215,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_212])).

tff(c_271,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_87,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66])).

tff(c_96,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_87])).

tff(c_230,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_96])).

tff(c_229,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_124])).

tff(c_321,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_partfun1(C_73,A_74)
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | v1_xboole_0(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_324,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_229,c_321])).

tff(c_327,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_230,c_324])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_271,c_327])).

tff(c_330,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_334,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_230])).

tff(c_332,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_229])).

tff(c_2141,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( r2_funct_2(A_198,B_199,C_200,C_200)
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_2(D_201,A_198,B_199)
      | ~ v1_funct_1(D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_2(C_200,A_198,B_199)
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2145,plain,(
    ! [C_200] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_200,C_200)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_200,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_200) ) ),
    inference(resolution,[status(thm)],[c_332,c_2141])).

tff(c_2172,plain,(
    ! [C_208] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_208,C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_208,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334,c_2145])).

tff(c_2177,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_332,c_2172])).

tff(c_2181,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334,c_2177])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_funct_1(k2_funct_1(A_14)) = A_14
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_226,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_220])).

tff(c_333,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_226])).

tff(c_1758,plain,(
    ! [C_179,A_180,B_181] :
      ( v1_funct_1(k2_funct_1(C_179))
      | k2_relset_1(A_180,B_181,C_179) != B_181
      | ~ v2_funct_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2(C_179,A_180,B_181)
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1761,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_332,c_1758])).

tff(c_1764,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334,c_60,c_333,c_1761])).

tff(c_1834,plain,(
    ! [C_184,B_185,A_186] :
      ( v1_funct_2(k2_funct_1(C_184),B_185,A_186)
      | k2_relset_1(A_186,B_185,C_184) != B_185
      | ~ v2_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185)))
      | ~ v1_funct_2(C_184,A_186,B_185)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1837,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_332,c_1834])).

tff(c_1840,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334,c_60,c_333,c_1837])).

tff(c_168,plain,(
    ! [A_63] :
      ( k4_relat_1(A_63) = k2_funct_1(A_63)
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_174,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_168])).

tff(c_180,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_68,c_174])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_188,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_6])).

tff(c_194,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_188])).

tff(c_1987,plain,(
    ! [C_190,B_191,A_192] :
      ( m1_subset_1(k2_funct_1(C_190),k1_zfmisc_1(k2_zfmisc_1(B_191,A_192)))
      | k2_relset_1(A_192,B_191,C_190) != B_191
      | ~ v2_funct_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191)))
      | ~ v1_funct_2(C_190,A_192,B_191)
      | ~ v1_funct_1(C_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_34,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2302,plain,(
    ! [B_212,A_213,C_214] :
      ( k2_relset_1(B_212,A_213,k2_funct_1(C_214)) = k2_relat_1(k2_funct_1(C_214))
      | k2_relset_1(A_213,B_212,C_214) != B_212
      | ~ v2_funct_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212)))
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ v1_funct_1(C_214) ) ),
    inference(resolution,[status(thm)],[c_1987,c_34])).

tff(c_2308,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_332,c_2302])).

tff(c_2312,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334,c_60,c_333,c_194,c_2308])).

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

tff(c_185,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_8])).

tff(c_192,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_185])).

tff(c_40,plain,(
    ! [B_26] :
      ( v1_partfun1(B_26,k1_relat_1(B_26))
      | ~ v4_relat_1(B_26,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_199,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_40])).

tff(c_202,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_199])).

tff(c_414,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_418,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_414])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_68,c_418])).

tff(c_424,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_202])).

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

tff(c_1714,plain,(
    ! [B_176,A_177] :
      ( v2_funct_1(B_176)
      | k2_relat_1(B_176) != k1_relat_1(A_177)
      | ~ v2_funct_1(k5_relat_1(B_176,A_177))
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176)
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1717,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1714])).

tff(c_1722,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | k2_relat_1(k2_funct_1(A_13)) != k1_relat_1(A_13)
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1717])).

tff(c_402,plain,(
    ! [A_77] :
      ( k5_relat_1(k2_funct_1(A_77),A_77) = k6_relat_1(k2_relat_1(A_77))
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1773,plain,(
    ! [A_183] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(A_183))) = k5_relat_1(A_183,k2_funct_1(A_183))
      | ~ v2_funct_1(k2_funct_1(A_183))
      | ~ v1_funct_1(k2_funct_1(A_183))
      | ~ v1_relat_1(k2_funct_1(A_183))
      | ~ v2_funct_1(A_183)
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_402])).

tff(c_1807,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_1773])).

tff(c_1820,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_68,c_60,c_424,c_1764,c_1807])).

tff(c_1821,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1820])).

tff(c_1824,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1722,c_1821])).

tff(c_1831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_68,c_60,c_424,c_1764,c_194,c_1824])).

tff(c_1833,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1820])).

tff(c_56,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_tops_2(A_36,B_37,C_38) = k2_funct_1(C_38)
      | ~ v2_funct_1(C_38)
      | k2_relset_1(A_36,B_37,C_38) != B_37
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3589,plain,(
    ! [B_253,A_254,C_255] :
      ( k2_tops_2(B_253,A_254,k2_funct_1(C_255)) = k2_funct_1(k2_funct_1(C_255))
      | ~ v2_funct_1(k2_funct_1(C_255))
      | k2_relset_1(B_253,A_254,k2_funct_1(C_255)) != A_254
      | ~ v1_funct_2(k2_funct_1(C_255),B_253,A_254)
      | ~ v1_funct_1(k2_funct_1(C_255))
      | k2_relset_1(A_254,B_253,C_255) != B_253
      | ~ v2_funct_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_254,B_253)))
      | ~ v1_funct_2(C_255,A_254,B_253)
      | ~ v1_funct_1(C_255) ) ),
    inference(resolution,[status(thm)],[c_1987,c_56])).

tff(c_3595,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_332,c_3589])).

tff(c_3599,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334,c_60,c_333,c_1764,c_1840,c_2312,c_1833,c_3595])).

tff(c_1932,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_tops_2(A_187,B_188,C_189) = k2_funct_1(C_189)
      | ~ v2_funct_1(C_189)
      | k2_relset_1(A_187,B_188,C_189) != B_188
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(C_189,A_187,B_188)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1935,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_332,c_1932])).

tff(c_1938,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334,c_333,c_60,c_1935])).

tff(c_58,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_181,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_86,c_85,c_85,c_85,c_58])).

tff(c_227,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_221,c_221,c_181])).

tff(c_1749,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_330,c_330,c_227])).

tff(c_1965,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1749])).

tff(c_3600,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3599,c_1965])).

tff(c_3607,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3600])).

tff(c_3610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_68,c_60,c_2181,c_3607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.85/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.85/2.44  
% 6.85/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.85/2.44  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.85/2.44  
% 6.85/2.44  %Foreground sorts:
% 6.85/2.44  
% 6.85/2.44  
% 6.85/2.44  %Background operators:
% 6.85/2.44  
% 6.85/2.44  
% 6.85/2.44  %Foreground operators:
% 6.85/2.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.85/2.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.85/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.85/2.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.85/2.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.85/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.85/2.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.85/2.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.85/2.44  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.85/2.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.85/2.44  tff('#skF_2', type, '#skF_2': $i).
% 6.85/2.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.85/2.44  tff('#skF_3', type, '#skF_3': $i).
% 6.85/2.44  tff('#skF_1', type, '#skF_1': $i).
% 6.85/2.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.85/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.85/2.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.85/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.85/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.85/2.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.85/2.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.85/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.85/2.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.85/2.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.85/2.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.85/2.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.85/2.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.85/2.44  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.85/2.44  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.85/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.85/2.44  
% 6.85/2.47  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.85/2.47  tff(f_203, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 6.85/2.47  tff(f_161, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.85/2.47  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.85/2.47  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.85/2.47  tff(f_169, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 6.85/2.47  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.85/2.47  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 6.85/2.47  tff(f_119, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 6.85/2.47  tff(f_141, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 6.85/2.47  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 6.85/2.47  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.85/2.47  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 6.85/2.47  tff(f_40, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 6.85/2.47  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.85/2.47  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.85/2.47  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.85/2.47  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 6.85/2.47  tff(f_181, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 6.85/2.47  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.85/2.47  tff(c_74, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_78, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.85/2.47  tff(c_86, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_78])).
% 6.85/2.47  tff(c_70, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_85, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_78])).
% 6.85/2.47  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_124, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_64])).
% 6.85/2.47  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.85/2.47  tff(c_127, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_124, c_2])).
% 6.85/2.47  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_127])).
% 6.85/2.47  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_216, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.85/2.47  tff(c_220, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_216])).
% 6.85/2.47  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_119, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_62])).
% 6.85/2.47  tff(c_221, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_119])).
% 6.85/2.47  tff(c_54, plain, (![A_35]: (~v1_xboole_0(k2_struct_0(A_35)) | ~l1_struct_0(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.85/2.47  tff(c_235, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_221, c_54])).
% 6.85/2.47  tff(c_239, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_235])).
% 6.85/2.47  tff(c_240, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_239])).
% 6.85/2.47  tff(c_136, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.85/2.47  tff(c_140, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_124, c_136])).
% 6.85/2.47  tff(c_209, plain, (![B_65, A_66]: (k1_relat_1(B_65)=A_66 | ~v1_partfun1(B_65, A_66) | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.85/2.47  tff(c_212, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_140, c_209])).
% 6.85/2.47  tff(c_215, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_212])).
% 6.85/2.47  tff(c_271, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_215])).
% 6.85/2.47  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_87, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66])).
% 6.85/2.47  tff(c_96, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_87])).
% 6.85/2.47  tff(c_230, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_96])).
% 6.85/2.47  tff(c_229, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_124])).
% 6.85/2.47  tff(c_321, plain, (![C_73, A_74, B_75]: (v1_partfun1(C_73, A_74) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | v1_xboole_0(B_75))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.85/2.47  tff(c_324, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_229, c_321])).
% 6.85/2.47  tff(c_327, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_230, c_324])).
% 6.85/2.47  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_271, c_327])).
% 6.85/2.47  tff(c_330, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_215])).
% 6.85/2.47  tff(c_334, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_230])).
% 6.85/2.47  tff(c_332, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_229])).
% 6.85/2.47  tff(c_2141, plain, (![A_198, B_199, C_200, D_201]: (r2_funct_2(A_198, B_199, C_200, C_200) | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_2(D_201, A_198, B_199) | ~v1_funct_1(D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_2(C_200, A_198, B_199) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.85/2.47  tff(c_2145, plain, (![C_200]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_200, C_200) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_200, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_200))), inference(resolution, [status(thm)], [c_332, c_2141])).
% 6.85/2.47  tff(c_2172, plain, (![C_208]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_208, C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_208, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_208))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334, c_2145])).
% 6.85/2.47  tff(c_2177, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_332, c_2172])).
% 6.85/2.47  tff(c_2181, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334, c_2177])).
% 6.85/2.47  tff(c_28, plain, (![A_14]: (k2_funct_1(k2_funct_1(A_14))=A_14 | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.85/2.47  tff(c_226, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_220])).
% 6.85/2.47  tff(c_333, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_226])).
% 6.85/2.47  tff(c_1758, plain, (![C_179, A_180, B_181]: (v1_funct_1(k2_funct_1(C_179)) | k2_relset_1(A_180, B_181, C_179)!=B_181 | ~v2_funct_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2(C_179, A_180, B_181) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.85/2.47  tff(c_1761, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_332, c_1758])).
% 6.85/2.47  tff(c_1764, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334, c_60, c_333, c_1761])).
% 6.85/2.47  tff(c_1834, plain, (![C_184, B_185, A_186]: (v1_funct_2(k2_funct_1(C_184), B_185, A_186) | k2_relset_1(A_186, B_185, C_184)!=B_185 | ~v2_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))) | ~v1_funct_2(C_184, A_186, B_185) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.85/2.47  tff(c_1837, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_332, c_1834])).
% 6.85/2.47  tff(c_1840, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334, c_60, c_333, c_1837])).
% 6.85/2.47  tff(c_168, plain, (![A_63]: (k4_relat_1(A_63)=k2_funct_1(A_63) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.85/2.47  tff(c_174, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_168])).
% 6.85/2.47  tff(c_180, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_68, c_174])).
% 6.85/2.47  tff(c_6, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.85/2.47  tff(c_188, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_180, c_6])).
% 6.85/2.47  tff(c_194, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_188])).
% 6.85/2.47  tff(c_1987, plain, (![C_190, B_191, A_192]: (m1_subset_1(k2_funct_1(C_190), k1_zfmisc_1(k2_zfmisc_1(B_191, A_192))) | k2_relset_1(A_192, B_191, C_190)!=B_191 | ~v2_funct_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))) | ~v1_funct_2(C_190, A_192, B_191) | ~v1_funct_1(C_190))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.85/2.47  tff(c_34, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.85/2.47  tff(c_2302, plain, (![B_212, A_213, C_214]: (k2_relset_1(B_212, A_213, k2_funct_1(C_214))=k2_relat_1(k2_funct_1(C_214)) | k2_relset_1(A_213, B_212, C_214)!=B_212 | ~v2_funct_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))) | ~v1_funct_2(C_214, A_213, B_212) | ~v1_funct_1(C_214))), inference(resolution, [status(thm)], [c_1987, c_34])).
% 6.85/2.47  tff(c_2308, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_332, c_2302])).
% 6.85/2.47  tff(c_2312, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334, c_60, c_333, c_194, c_2308])).
% 6.85/2.47  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.85/2.47  tff(c_8, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.85/2.47  tff(c_185, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_180, c_8])).
% 6.85/2.47  tff(c_192, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_185])).
% 6.85/2.47  tff(c_40, plain, (![B_26]: (v1_partfun1(B_26, k1_relat_1(B_26)) | ~v4_relat_1(B_26, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.85/2.47  tff(c_199, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_192, c_40])).
% 6.85/2.47  tff(c_202, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_199])).
% 6.85/2.47  tff(c_414, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_202])).
% 6.85/2.47  tff(c_418, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_414])).
% 6.85/2.47  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_68, c_418])).
% 6.85/2.47  tff(c_424, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_202])).
% 6.85/2.47  tff(c_18, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.85/2.47  tff(c_24, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_relat_1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.85/2.47  tff(c_1714, plain, (![B_176, A_177]: (v2_funct_1(B_176) | k2_relat_1(B_176)!=k1_relat_1(A_177) | ~v2_funct_1(k5_relat_1(B_176, A_177)) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.85/2.47  tff(c_1717, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_13))) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1714])).
% 6.85/2.47  tff(c_1722, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | k2_relat_1(k2_funct_1(A_13))!=k1_relat_1(A_13) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1717])).
% 6.85/2.47  tff(c_402, plain, (![A_77]: (k5_relat_1(k2_funct_1(A_77), A_77)=k6_relat_1(k2_relat_1(A_77)) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.85/2.47  tff(c_1773, plain, (![A_183]: (k6_relat_1(k2_relat_1(k2_funct_1(A_183)))=k5_relat_1(A_183, k2_funct_1(A_183)) | ~v2_funct_1(k2_funct_1(A_183)) | ~v1_funct_1(k2_funct_1(A_183)) | ~v1_relat_1(k2_funct_1(A_183)) | ~v2_funct_1(A_183) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_28, c_402])).
% 6.85/2.47  tff(c_1807, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_194, c_1773])).
% 6.85/2.47  tff(c_1820, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_68, c_60, c_424, c_1764, c_1807])).
% 6.85/2.47  tff(c_1821, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1820])).
% 6.85/2.47  tff(c_1824, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1722, c_1821])).
% 6.85/2.47  tff(c_1831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_68, c_60, c_424, c_1764, c_194, c_1824])).
% 6.85/2.47  tff(c_1833, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1820])).
% 6.85/2.47  tff(c_56, plain, (![A_36, B_37, C_38]: (k2_tops_2(A_36, B_37, C_38)=k2_funct_1(C_38) | ~v2_funct_1(C_38) | k2_relset_1(A_36, B_37, C_38)!=B_37 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(C_38, A_36, B_37) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.85/2.47  tff(c_3589, plain, (![B_253, A_254, C_255]: (k2_tops_2(B_253, A_254, k2_funct_1(C_255))=k2_funct_1(k2_funct_1(C_255)) | ~v2_funct_1(k2_funct_1(C_255)) | k2_relset_1(B_253, A_254, k2_funct_1(C_255))!=A_254 | ~v1_funct_2(k2_funct_1(C_255), B_253, A_254) | ~v1_funct_1(k2_funct_1(C_255)) | k2_relset_1(A_254, B_253, C_255)!=B_253 | ~v2_funct_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))) | ~v1_funct_2(C_255, A_254, B_253) | ~v1_funct_1(C_255))), inference(resolution, [status(thm)], [c_1987, c_56])).
% 6.85/2.47  tff(c_3595, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_332, c_3589])).
% 6.85/2.47  tff(c_3599, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334, c_60, c_333, c_1764, c_1840, c_2312, c_1833, c_3595])).
% 6.85/2.47  tff(c_1932, plain, (![A_187, B_188, C_189]: (k2_tops_2(A_187, B_188, C_189)=k2_funct_1(C_189) | ~v2_funct_1(C_189) | k2_relset_1(A_187, B_188, C_189)!=B_188 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(C_189, A_187, B_188) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.85/2.47  tff(c_1935, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_332, c_1932])).
% 6.85/2.47  tff(c_1938, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334, c_333, c_60, c_1935])).
% 6.85/2.47  tff(c_58, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.85/2.47  tff(c_181, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_86, c_85, c_85, c_85, c_58])).
% 6.85/2.47  tff(c_227, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_221, c_221, c_181])).
% 6.85/2.47  tff(c_1749, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_330, c_330, c_227])).
% 6.85/2.47  tff(c_1965, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1749])).
% 6.85/2.47  tff(c_3600, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3599, c_1965])).
% 6.85/2.47  tff(c_3607, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_3600])).
% 6.85/2.47  tff(c_3610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_68, c_60, c_2181, c_3607])).
% 6.85/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.85/2.47  
% 6.85/2.47  Inference rules
% 6.85/2.47  ----------------------
% 6.85/2.47  #Ref     : 0
% 6.85/2.47  #Sup     : 770
% 6.85/2.47  #Fact    : 0
% 6.85/2.47  #Define  : 0
% 6.85/2.47  #Split   : 23
% 6.85/2.47  #Chain   : 0
% 6.85/2.47  #Close   : 0
% 6.85/2.47  
% 6.85/2.47  Ordering : KBO
% 6.85/2.47  
% 6.85/2.47  Simplification rules
% 6.85/2.47  ----------------------
% 6.85/2.47  #Subsume      : 38
% 6.85/2.47  #Demod        : 2026
% 6.85/2.47  #Tautology    : 444
% 6.85/2.47  #SimpNegUnit  : 6
% 6.85/2.47  #BackRed      : 40
% 6.85/2.47  
% 6.85/2.47  #Partial instantiations: 0
% 6.85/2.47  #Strategies tried      : 1
% 6.85/2.47  
% 6.85/2.47  Timing (in seconds)
% 6.85/2.47  ----------------------
% 6.85/2.47  Preprocessing        : 0.49
% 6.85/2.47  Parsing              : 0.29
% 6.85/2.47  CNF conversion       : 0.03
% 6.85/2.47  Main loop            : 1.10
% 6.85/2.47  Inferencing          : 0.38
% 6.85/2.47  Reduction            : 0.41
% 6.85/2.47  Demodulation         : 0.30
% 6.85/2.47  BG Simplification    : 0.05
% 6.85/2.47  Subsumption          : 0.19
% 6.85/2.47  Abstraction          : 0.05
% 6.85/2.47  MUC search           : 0.00
% 6.85/2.47  Cooper               : 0.00
% 6.85/2.47  Total                : 1.65
% 6.85/2.47  Index Insertion      : 0.00
% 6.85/2.47  Index Deletion       : 0.00
% 6.85/2.47  Index Matching       : 0.00
% 6.85/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
