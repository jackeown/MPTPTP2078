%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:37 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  169 (15213 expanded)
%              Number of leaves         :   48 (5298 expanded)
%              Depth                    :   24
%              Number of atoms          :  425 (43490 expanded)
%              Number of equality atoms :   77 (9418 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_205,negated_conjecture,(
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

tff(f_163,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
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

tff(f_171,axiom,(
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

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_159,axiom,(
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

tff(f_52,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_183,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_84,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_92,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_84])).

tff(c_74,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_91,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_84])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_91,c_68])).

tff(c_119,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_106,c_119])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_122])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_196,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_200,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_196])).

tff(c_66,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_114,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_91,c_66])).

tff(c_213,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_114])).

tff(c_58,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k2_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_227,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_58])).

tff(c_231,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_227])).

tff(c_232,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_231])).

tff(c_131,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_135,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_106,c_131])).

tff(c_188,plain,(
    ! [B_67,A_68] :
      ( k1_relat_1(B_67) = A_68
      | ~ v1_partfun1(B_67,A_68)
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_191,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_188])).

tff(c_194,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_191])).

tff(c_195,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_93,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_70])).

tff(c_102,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_93])).

tff(c_222,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_102])).

tff(c_221,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_106])).

tff(c_275,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_partfun1(C_74,A_75)
      | ~ v1_funct_2(C_74,A_75,B_76)
      | ~ v1_funct_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | v1_xboole_0(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_278,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_221,c_275])).

tff(c_281,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_222,c_278])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_195,c_281])).

tff(c_284,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_289,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_106])).

tff(c_340,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_344,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_340])).

tff(c_288,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_114])).

tff(c_345,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_288])).

tff(c_290,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_102])).

tff(c_352,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_290])).

tff(c_351,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_289])).

tff(c_418,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_funct_2(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(D_84,A_82,B_83)
      | ~ v1_funct_1(D_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_420,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_418])).

tff(c_423,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_420])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_funct_1(k2_funct_1(A_15)) = A_15
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_350,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_344])).

tff(c_450,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_funct_1(k2_funct_1(C_91))
      | k2_relset_1(A_92,B_93,C_91) != B_93
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2(C_91,A_92,B_93)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_453,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_450])).

tff(c_456,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_64,c_350,c_453])).

tff(c_457,plain,(
    ! [C_94,B_95,A_96] :
      ( v1_funct_2(k2_funct_1(C_94),B_95,A_96)
      | k2_relset_1(A_96,B_95,C_94) != B_95
      | ~ v2_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_2(C_94,A_96,B_95)
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_460,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_457])).

tff(c_463,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_64,c_350,c_460])).

tff(c_566,plain,(
    ! [C_104,B_105,A_106] :
      ( m1_subset_1(k2_funct_1(C_104),k1_zfmisc_1(k2_zfmisc_1(B_105,A_106)))
      | k2_relset_1(A_106,B_105,C_104) != B_105
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_104,A_106,B_105)
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1062,plain,(
    ! [B_149,A_150,C_151] :
      ( k2_relset_1(B_149,A_150,k2_funct_1(C_151)) = k2_relat_1(k2_funct_1(C_151))
      | k2_relset_1(A_150,B_149,C_151) != B_149
      | ~ v2_funct_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149)))
      | ~ v1_funct_2(C_151,A_150,B_149)
      | ~ v1_funct_1(C_151) ) ),
    inference(resolution,[status(thm)],[c_566,c_36])).

tff(c_1068,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_1062])).

tff(c_1072,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_64,c_350,c_1068])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_592,plain,(
    ! [C_104,B_105,A_106] :
      ( v1_relat_1(k2_funct_1(C_104))
      | ~ v1_relat_1(k2_zfmisc_1(B_105,A_106))
      | k2_relset_1(A_106,B_105,C_104) != B_105
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_104,A_106,B_105)
      | ~ v1_funct_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_566,c_8])).

tff(c_631,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_relat_1(k2_funct_1(C_109))
      | k2_relset_1(A_110,B_111,C_109) != B_111
      | ~ v2_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_2(C_109,A_110,B_111)
      | ~ v1_funct_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_592])).

tff(c_637,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_631])).

tff(c_641,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_64,c_350,c_637])).

tff(c_18,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_relat_1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_433,plain,(
    ! [B_88,A_89] :
      ( v2_funct_1(B_88)
      | ~ r1_tarski(k2_relat_1(B_88),k1_relat_1(A_89))
      | ~ v2_funct_1(k5_relat_1(B_88,A_89))
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_876,plain,(
    ! [A_137,A_138] :
      ( v2_funct_1(k2_funct_1(A_137))
      | ~ r1_tarski(k1_relat_1(A_137),k1_relat_1(A_138))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(A_137),A_138))
      | ~ v1_funct_1(k2_funct_1(A_137))
      | ~ v1_relat_1(k2_funct_1(A_137))
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138)
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_433])).

tff(c_898,plain,(
    ! [A_139] :
      ( v2_funct_1(k2_funct_1(A_139))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(A_139),A_139))
      | ~ v1_funct_1(k2_funct_1(A_139))
      | ~ v1_relat_1(k2_funct_1(A_139))
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_876])).

tff(c_907,plain,(
    ! [A_14] :
      ( v2_funct_1(k2_funct_1(A_14))
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_14)))
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_898])).

tff(c_916,plain,(
    ! [A_140] :
      ( v2_funct_1(k2_funct_1(A_140))
      | ~ v1_funct_1(k2_funct_1(A_140))
      | ~ v1_relat_1(k2_funct_1(A_140))
      | ~ v2_funct_1(A_140)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_907])).

tff(c_34,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_653,plain,(
    ! [C_115,B_116,A_117] :
      ( v4_relat_1(k2_funct_1(C_115),B_116)
      | k2_relset_1(A_117,B_116,C_115) != B_116
      | ~ v2_funct_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(C_115,A_117,B_116)
      | ~ v1_funct_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_566,c_34])).

tff(c_659,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_653])).

tff(c_663,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_64,c_350,c_659])).

tff(c_44,plain,(
    ! [B_27,A_26] :
      ( k1_relat_1(B_27) = A_26
      | ~ v1_partfun1(B_27,A_26)
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_666,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_663,c_44])).

tff(c_669,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_666])).

tff(c_670,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_24,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_173,plain,(
    ! [A_66] :
      ( k1_relat_1(k2_funct_1(A_66)) = k2_relat_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [B_27] :
      ( v1_partfun1(B_27,k1_relat_1(B_27))
      | ~ v4_relat_1(B_27,k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_440,plain,(
    ! [A_90] :
      ( v1_partfun1(k2_funct_1(A_90),k1_relat_1(k2_funct_1(A_90)))
      | ~ v4_relat_1(k2_funct_1(A_90),k2_relat_1(A_90))
      | ~ v1_relat_1(k2_funct_1(A_90))
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_42])).

tff(c_678,plain,(
    ! [A_122] :
      ( v1_partfun1(k2_funct_1(A_122),k2_relat_1(A_122))
      | ~ v4_relat_1(k2_funct_1(A_122),k2_relat_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122)
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_440])).

tff(c_681,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_663,c_678])).

tff(c_690,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_64,c_641,c_681])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_670,c_690])).

tff(c_693,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_406,plain,(
    ! [A_81] :
      ( k5_relat_1(A_81,k2_funct_1(A_81)) = k6_relat_1(k1_relat_1(A_81))
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_415,plain,(
    ! [A_15] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_15))) = k5_relat_1(k2_funct_1(A_15),A_15)
      | ~ v2_funct_1(k2_funct_1(A_15))
      | ~ v1_funct_1(k2_funct_1(A_15))
      | ~ v1_relat_1(k2_funct_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_406])).

tff(c_698,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_415])).

tff(c_717,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_64,c_641,c_456,c_698])).

tff(c_733,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_919,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_916,c_733])).

tff(c_926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_64,c_641,c_456,c_919])).

tff(c_928,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_60,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_tops_2(A_37,B_38,C_39) = k2_funct_1(C_39)
      | ~ v2_funct_1(C_39)
      | k2_relset_1(A_37,B_38,C_39) != B_38
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1659,plain,(
    ! [B_182,A_183,C_184] :
      ( k2_tops_2(B_182,A_183,k2_funct_1(C_184)) = k2_funct_1(k2_funct_1(C_184))
      | ~ v2_funct_1(k2_funct_1(C_184))
      | k2_relset_1(B_182,A_183,k2_funct_1(C_184)) != A_183
      | ~ v1_funct_2(k2_funct_1(C_184),B_182,A_183)
      | ~ v1_funct_1(k2_funct_1(C_184))
      | k2_relset_1(A_183,B_182,C_184) != B_182
      | ~ v2_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ v1_funct_1(C_184) ) ),
    inference(resolution,[status(thm)],[c_566,c_60])).

tff(c_1665,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_1659])).

tff(c_1669,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_64,c_350,c_456,c_463,c_1072,c_928,c_1665])).

tff(c_1671,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1669])).

tff(c_1674,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1671])).

tff(c_1678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_64,c_1674])).

tff(c_1679,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1669])).

tff(c_497,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_tops_2(A_98,B_99,C_100) = k2_funct_1(C_100)
      | ~ v2_funct_1(C_100)
      | k2_relset_1(A_98,B_99,C_100) != B_99
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_2(C_100,A_98,B_99)
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_500,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_497])).

tff(c_503,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352,c_350,c_64,c_500])).

tff(c_62,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_172,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_92,c_92,c_91,c_91,c_91,c_62])).

tff(c_286,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_284,c_284,c_172])).

tff(c_424,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_345,c_345,c_286])).

tff(c_504,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_424])).

tff(c_1774,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_504])).

tff(c_1781,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1774])).

tff(c_1784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_64,c_423,c_1781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.92  
% 5.02/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.92  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.02/1.92  
% 5.02/1.92  %Foreground sorts:
% 5.02/1.92  
% 5.02/1.92  
% 5.02/1.92  %Background operators:
% 5.02/1.92  
% 5.02/1.92  
% 5.02/1.92  %Foreground operators:
% 5.02/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.02/1.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.02/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.02/1.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.02/1.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/1.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.02/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.02/1.92  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.02/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.02/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.02/1.92  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.02/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.02/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.02/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.02/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.02/1.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.02/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.02/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.02/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.02/1.92  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.02/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.02/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.02/1.92  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.02/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.02/1.92  
% 5.02/1.95  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.02/1.95  tff(f_205, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 5.02/1.95  tff(f_163, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.02/1.95  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.02/1.95  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.02/1.95  tff(f_171, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.02/1.95  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.02/1.95  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.02/1.95  tff(f_119, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.02/1.95  tff(f_143, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.02/1.95  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.02/1.95  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.02/1.95  tff(f_159, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.02/1.95  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.02/1.95  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.02/1.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.02/1.95  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 5.02/1.95  tff(f_183, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.02/1.95  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.02/1.95  tff(c_78, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_84, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.02/1.95  tff(c_92, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_84])).
% 5.02/1.95  tff(c_74, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_91, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_84])).
% 5.02/1.95  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_91, c_68])).
% 5.02/1.95  tff(c_119, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.02/1.95  tff(c_122, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_106, c_119])).
% 5.02/1.95  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_122])).
% 5.02/1.95  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_196, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.02/1.95  tff(c_200, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_196])).
% 5.02/1.95  tff(c_66, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_114, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_91, c_66])).
% 5.02/1.95  tff(c_213, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_114])).
% 5.02/1.95  tff(c_58, plain, (![A_36]: (~v1_xboole_0(k2_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.02/1.95  tff(c_227, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_213, c_58])).
% 5.02/1.95  tff(c_231, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_227])).
% 5.02/1.95  tff(c_232, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_231])).
% 5.02/1.95  tff(c_131, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.02/1.95  tff(c_135, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_106, c_131])).
% 5.02/1.95  tff(c_188, plain, (![B_67, A_68]: (k1_relat_1(B_67)=A_68 | ~v1_partfun1(B_67, A_68) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.02/1.95  tff(c_191, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_188])).
% 5.02/1.95  tff(c_194, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_191])).
% 5.02/1.95  tff(c_195, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_194])).
% 5.02/1.95  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_93, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_70])).
% 5.02/1.95  tff(c_102, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_93])).
% 5.02/1.95  tff(c_222, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_102])).
% 5.02/1.95  tff(c_221, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_106])).
% 5.02/1.95  tff(c_275, plain, (![C_74, A_75, B_76]: (v1_partfun1(C_74, A_75) | ~v1_funct_2(C_74, A_75, B_76) | ~v1_funct_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | v1_xboole_0(B_76))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.95  tff(c_278, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_221, c_275])).
% 5.02/1.95  tff(c_281, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_222, c_278])).
% 5.02/1.95  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_195, c_281])).
% 5.02/1.95  tff(c_284, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_194])).
% 5.02/1.95  tff(c_289, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_106])).
% 5.02/1.95  tff(c_340, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.02/1.95  tff(c_344, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_340])).
% 5.02/1.95  tff(c_288, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_114])).
% 5.02/1.95  tff(c_345, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_288])).
% 5.02/1.95  tff(c_290, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_102])).
% 5.02/1.95  tff(c_352, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_290])).
% 5.02/1.95  tff(c_351, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_289])).
% 5.02/1.95  tff(c_418, plain, (![A_82, B_83, D_84]: (r2_funct_2(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(D_84, A_82, B_83) | ~v1_funct_1(D_84))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.02/1.95  tff(c_420, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_418])).
% 5.02/1.95  tff(c_423, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_420])).
% 5.02/1.95  tff(c_30, plain, (![A_15]: (k2_funct_1(k2_funct_1(A_15))=A_15 | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.02/1.95  tff(c_22, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.02/1.95  tff(c_350, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_344])).
% 5.02/1.95  tff(c_450, plain, (![C_91, A_92, B_93]: (v1_funct_1(k2_funct_1(C_91)) | k2_relset_1(A_92, B_93, C_91)!=B_93 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2(C_91, A_92, B_93) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.02/1.95  tff(c_453, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_450])).
% 5.02/1.95  tff(c_456, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_64, c_350, c_453])).
% 5.02/1.95  tff(c_457, plain, (![C_94, B_95, A_96]: (v1_funct_2(k2_funct_1(C_94), B_95, A_96) | k2_relset_1(A_96, B_95, C_94)!=B_95 | ~v2_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_2(C_94, A_96, B_95) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.02/1.95  tff(c_460, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_457])).
% 5.02/1.95  tff(c_463, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_64, c_350, c_460])).
% 5.02/1.95  tff(c_566, plain, (![C_104, B_105, A_106]: (m1_subset_1(k2_funct_1(C_104), k1_zfmisc_1(k2_zfmisc_1(B_105, A_106))) | k2_relset_1(A_106, B_105, C_104)!=B_105 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_104, A_106, B_105) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.02/1.95  tff(c_36, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.02/1.95  tff(c_1062, plain, (![B_149, A_150, C_151]: (k2_relset_1(B_149, A_150, k2_funct_1(C_151))=k2_relat_1(k2_funct_1(C_151)) | k2_relset_1(A_150, B_149, C_151)!=B_149 | ~v2_funct_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))) | ~v1_funct_2(C_151, A_150, B_149) | ~v1_funct_1(C_151))), inference(resolution, [status(thm)], [c_566, c_36])).
% 5.02/1.95  tff(c_1068, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_1062])).
% 5.02/1.95  tff(c_1072, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_64, c_350, c_1068])).
% 5.02/1.95  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.02/1.95  tff(c_592, plain, (![C_104, B_105, A_106]: (v1_relat_1(k2_funct_1(C_104)) | ~v1_relat_1(k2_zfmisc_1(B_105, A_106)) | k2_relset_1(A_106, B_105, C_104)!=B_105 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_104, A_106, B_105) | ~v1_funct_1(C_104))), inference(resolution, [status(thm)], [c_566, c_8])).
% 5.02/1.95  tff(c_631, plain, (![C_109, A_110, B_111]: (v1_relat_1(k2_funct_1(C_109)) | k2_relset_1(A_110, B_111, C_109)!=B_111 | ~v2_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_2(C_109, A_110, B_111) | ~v1_funct_1(C_109))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_592])).
% 5.02/1.95  tff(c_637, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_631])).
% 5.02/1.95  tff(c_641, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_64, c_350, c_637])).
% 5.02/1.95  tff(c_18, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.02/1.95  tff(c_26, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_relat_1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.02/1.95  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.02/1.95  tff(c_433, plain, (![B_88, A_89]: (v2_funct_1(B_88) | ~r1_tarski(k2_relat_1(B_88), k1_relat_1(A_89)) | ~v2_funct_1(k5_relat_1(B_88, A_89)) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.02/1.95  tff(c_876, plain, (![A_137, A_138]: (v2_funct_1(k2_funct_1(A_137)) | ~r1_tarski(k1_relat_1(A_137), k1_relat_1(A_138)) | ~v2_funct_1(k5_relat_1(k2_funct_1(A_137), A_138)) | ~v1_funct_1(k2_funct_1(A_137)) | ~v1_relat_1(k2_funct_1(A_137)) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138) | ~v2_funct_1(A_137) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(superposition, [status(thm), theory('equality')], [c_22, c_433])).
% 5.02/1.95  tff(c_898, plain, (![A_139]: (v2_funct_1(k2_funct_1(A_139)) | ~v2_funct_1(k5_relat_1(k2_funct_1(A_139), A_139)) | ~v1_funct_1(k2_funct_1(A_139)) | ~v1_relat_1(k2_funct_1(A_139)) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_6, c_876])).
% 5.02/1.95  tff(c_907, plain, (![A_14]: (v2_funct_1(k2_funct_1(A_14)) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_14))) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_26, c_898])).
% 5.02/1.95  tff(c_916, plain, (![A_140]: (v2_funct_1(k2_funct_1(A_140)) | ~v1_funct_1(k2_funct_1(A_140)) | ~v1_relat_1(k2_funct_1(A_140)) | ~v2_funct_1(A_140) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_907])).
% 5.02/1.95  tff(c_34, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.02/1.95  tff(c_653, plain, (![C_115, B_116, A_117]: (v4_relat_1(k2_funct_1(C_115), B_116) | k2_relset_1(A_117, B_116, C_115)!=B_116 | ~v2_funct_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(C_115, A_117, B_116) | ~v1_funct_1(C_115))), inference(resolution, [status(thm)], [c_566, c_34])).
% 5.02/1.95  tff(c_659, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_653])).
% 5.02/1.95  tff(c_663, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_64, c_350, c_659])).
% 5.02/1.95  tff(c_44, plain, (![B_27, A_26]: (k1_relat_1(B_27)=A_26 | ~v1_partfun1(B_27, A_26) | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.02/1.95  tff(c_666, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_663, c_44])).
% 5.02/1.95  tff(c_669, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_666])).
% 5.02/1.95  tff(c_670, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_669])).
% 5.02/1.95  tff(c_24, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.02/1.95  tff(c_173, plain, (![A_66]: (k1_relat_1(k2_funct_1(A_66))=k2_relat_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.02/1.95  tff(c_42, plain, (![B_27]: (v1_partfun1(B_27, k1_relat_1(B_27)) | ~v4_relat_1(B_27, k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.02/1.95  tff(c_440, plain, (![A_90]: (v1_partfun1(k2_funct_1(A_90), k1_relat_1(k2_funct_1(A_90))) | ~v4_relat_1(k2_funct_1(A_90), k2_relat_1(A_90)) | ~v1_relat_1(k2_funct_1(A_90)) | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_173, c_42])).
% 5.02/1.95  tff(c_678, plain, (![A_122]: (v1_partfun1(k2_funct_1(A_122), k2_relat_1(A_122)) | ~v4_relat_1(k2_funct_1(A_122), k2_relat_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_24, c_440])).
% 5.02/1.95  tff(c_681, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_663, c_678])).
% 5.02/1.95  tff(c_690, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_64, c_641, c_681])).
% 5.02/1.95  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_670, c_690])).
% 5.02/1.95  tff(c_693, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_669])).
% 5.02/1.95  tff(c_406, plain, (![A_81]: (k5_relat_1(A_81, k2_funct_1(A_81))=k6_relat_1(k1_relat_1(A_81)) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.02/1.95  tff(c_415, plain, (![A_15]: (k6_relat_1(k1_relat_1(k2_funct_1(A_15)))=k5_relat_1(k2_funct_1(A_15), A_15) | ~v2_funct_1(k2_funct_1(A_15)) | ~v1_funct_1(k2_funct_1(A_15)) | ~v1_relat_1(k2_funct_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_30, c_406])).
% 5.02/1.95  tff(c_698, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_693, c_415])).
% 5.02/1.95  tff(c_717, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_64, c_641, c_456, c_698])).
% 5.02/1.95  tff(c_733, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_717])).
% 5.02/1.95  tff(c_919, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_916, c_733])).
% 5.02/1.95  tff(c_926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_64, c_641, c_456, c_919])).
% 5.02/1.95  tff(c_928, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_717])).
% 5.02/1.95  tff(c_60, plain, (![A_37, B_38, C_39]: (k2_tops_2(A_37, B_38, C_39)=k2_funct_1(C_39) | ~v2_funct_1(C_39) | k2_relset_1(A_37, B_38, C_39)!=B_38 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(C_39, A_37, B_38) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.02/1.95  tff(c_1659, plain, (![B_182, A_183, C_184]: (k2_tops_2(B_182, A_183, k2_funct_1(C_184))=k2_funct_1(k2_funct_1(C_184)) | ~v2_funct_1(k2_funct_1(C_184)) | k2_relset_1(B_182, A_183, k2_funct_1(C_184))!=A_183 | ~v1_funct_2(k2_funct_1(C_184), B_182, A_183) | ~v1_funct_1(k2_funct_1(C_184)) | k2_relset_1(A_183, B_182, C_184)!=B_182 | ~v2_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_2(C_184, A_183, B_182) | ~v1_funct_1(C_184))), inference(resolution, [status(thm)], [c_566, c_60])).
% 5.02/1.95  tff(c_1665, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_1659])).
% 5.02/1.95  tff(c_1669, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_64, c_350, c_456, c_463, c_1072, c_928, c_1665])).
% 5.02/1.95  tff(c_1671, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1669])).
% 5.02/1.95  tff(c_1674, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1671])).
% 5.02/1.95  tff(c_1678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_64, c_1674])).
% 5.02/1.95  tff(c_1679, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1669])).
% 5.02/1.95  tff(c_497, plain, (![A_98, B_99, C_100]: (k2_tops_2(A_98, B_99, C_100)=k2_funct_1(C_100) | ~v2_funct_1(C_100) | k2_relset_1(A_98, B_99, C_100)!=B_99 | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_funct_2(C_100, A_98, B_99) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.02/1.95  tff(c_500, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_497])).
% 5.02/1.95  tff(c_503, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352, c_350, c_64, c_500])).
% 5.02/1.95  tff(c_62, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.02/1.95  tff(c_172, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_92, c_92, c_91, c_91, c_91, c_62])).
% 5.02/1.95  tff(c_286, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_284, c_284, c_172])).
% 5.02/1.95  tff(c_424, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_345, c_345, c_286])).
% 5.02/1.95  tff(c_504, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_424])).
% 5.02/1.95  tff(c_1774, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1679, c_504])).
% 5.02/1.95  tff(c_1781, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1774])).
% 5.02/1.95  tff(c_1784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_64, c_423, c_1781])).
% 5.02/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.95  
% 5.02/1.95  Inference rules
% 5.02/1.95  ----------------------
% 5.02/1.95  #Ref     : 0
% 5.02/1.95  #Sup     : 395
% 5.02/1.95  #Fact    : 0
% 5.02/1.95  #Define  : 0
% 5.02/1.95  #Split   : 11
% 5.02/1.95  #Chain   : 0
% 5.02/1.95  #Close   : 0
% 5.02/1.95  
% 5.02/1.95  Ordering : KBO
% 5.02/1.95  
% 5.02/1.95  Simplification rules
% 5.02/1.95  ----------------------
% 5.02/1.95  #Subsume      : 56
% 5.02/1.95  #Demod        : 631
% 5.02/1.95  #Tautology    : 210
% 5.02/1.95  #SimpNegUnit  : 6
% 5.02/1.95  #BackRed      : 24
% 5.02/1.95  
% 5.02/1.95  #Partial instantiations: 0
% 5.02/1.95  #Strategies tried      : 1
% 5.02/1.95  
% 5.02/1.95  Timing (in seconds)
% 5.02/1.95  ----------------------
% 5.02/1.96  Preprocessing        : 0.38
% 5.02/1.96  Parsing              : 0.21
% 5.02/1.96  CNF conversion       : 0.02
% 5.02/1.96  Main loop            : 0.76
% 5.02/1.96  Inferencing          : 0.27
% 5.02/1.96  Reduction            : 0.27
% 5.02/1.96  Demodulation         : 0.20
% 5.02/1.96  BG Simplification    : 0.04
% 5.02/1.96  Subsumption          : 0.14
% 5.02/1.96  Abstraction          : 0.03
% 5.02/1.96  MUC search           : 0.00
% 5.02/1.96  Cooper               : 0.00
% 5.02/1.96  Total                : 1.20
% 5.02/1.96  Index Insertion      : 0.00
% 5.02/1.96  Index Deletion       : 0.00
% 5.02/1.96  Index Matching       : 0.00
% 5.02/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
