%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:36 EST 2020

% Result     : Theorem 8.53s
% Output     : CNFRefutation 8.74s
% Verified   : 
% Statistics : Number of formulae       :  256 (28288 expanded)
%              Number of leaves         :   50 (9864 expanded)
%              Depth                    :   28
%              Number of atoms          :  546 (79996 expanded)
%              Number of equality atoms :  111 (16794 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_207,negated_conjecture,(
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

tff(f_165,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_135,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_151,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_161,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_185,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_86,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_93,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_86])).

tff(c_82,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_94,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_86])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_6780,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_94,c_72])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6783,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6780,c_8])).

tff(c_6786,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6783])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_6938,plain,(
    ! [A_430,B_431,C_432] :
      ( k2_relset_1(A_430,B_431,C_432) = k2_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6946,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6780,c_6938])).

tff(c_70,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_6767,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_94,c_70])).

tff(c_6947,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6946,c_6767])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_105,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(u1_struct_0(A_52))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_111,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_105])).

tff(c_115,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_111])).

tff(c_116,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_115])).

tff(c_6956,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6947,c_116])).

tff(c_6817,plain,(
    ! [C_413,A_414,B_415] :
      ( v4_relat_1(C_413,A_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6821,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6780,c_6817])).

tff(c_6885,plain,(
    ! [B_424,A_425] :
      ( k1_relat_1(B_424) = A_425
      | ~ v1_partfun1(B_424,A_425)
      | ~ v4_relat_1(B_424,A_425)
      | ~ v1_relat_1(B_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6888,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6821,c_6885])).

tff(c_6891,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_6888])).

tff(c_6892,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6891])).

tff(c_74,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_99,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_74])).

tff(c_100,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_99])).

tff(c_6957,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6947,c_100])).

tff(c_6955,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6947,c_6780])).

tff(c_7113,plain,(
    ! [C_445,A_446,B_447] :
      ( v1_partfun1(C_445,A_446)
      | ~ v1_funct_2(C_445,A_446,B_447)
      | ~ v1_funct_1(C_445)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | v1_xboole_0(B_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7116,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6955,c_7113])).

tff(c_7122,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6957,c_7116])).

tff(c_7124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6956,c_6892,c_7122])).

tff(c_7125,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6891])).

tff(c_7131,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7125,c_6780])).

tff(c_7237,plain,(
    ! [A_451,B_452,C_453] :
      ( k2_relset_1(A_451,B_452,C_453) = k2_relat_1(C_453)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(A_451,B_452))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7244,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7131,c_7237])).

tff(c_7132,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7125,c_6767])).

tff(c_7246,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7244,c_7132])).

tff(c_7134,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7125,c_100])).

tff(c_7253,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7246,c_7134])).

tff(c_7252,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7246,c_7131])).

tff(c_7643,plain,(
    ! [A_481,B_482,D_483] :
      ( r2_funct_2(A_481,B_482,D_483,D_483)
      | ~ m1_subset_1(D_483,k1_zfmisc_1(k2_zfmisc_1(A_481,B_482)))
      | ~ v1_funct_2(D_483,A_481,B_482)
      | ~ v1_funct_1(D_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_7645,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_7643])).

tff(c_7650,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_7645])).

tff(c_28,plain,(
    ! [A_18] :
      ( k2_funct_1(k2_funct_1(A_18)) = A_18
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7251,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7246,c_7244])).

tff(c_7652,plain,(
    ! [C_484,A_485,B_486] :
      ( v1_funct_1(k2_funct_1(C_484))
      | k2_relset_1(A_485,B_486,C_484) != B_486
      | ~ v2_funct_1(C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486)))
      | ~ v1_funct_2(C_484,A_485,B_486)
      | ~ v1_funct_1(C_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_7655,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_7652])).

tff(c_7661,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_68,c_7251,c_7655])).

tff(c_8433,plain,(
    ! [C_537,B_538,A_539] :
      ( v1_funct_2(k2_funct_1(C_537),B_538,A_539)
      | k2_relset_1(A_539,B_538,C_537) != B_538
      | ~ v2_funct_1(C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_539,B_538)))
      | ~ v1_funct_2(C_537,A_539,B_538)
      | ~ v1_funct_1(C_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8436,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_8433])).

tff(c_8442,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_68,c_7251,c_8436])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6833,plain,(
    ! [B_418,A_419] :
      ( k7_relat_1(B_418,A_419) = B_418
      | ~ v4_relat_1(B_418,A_419)
      | ~ v1_relat_1(B_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6836,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6821,c_6833])).

tff(c_6839,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_6836])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6843,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6839,c_16])).

tff(c_6847,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_6843])).

tff(c_7127,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7125,c_6847])).

tff(c_7494,plain,(
    ! [A_471,B_472] :
      ( k9_relat_1(k2_funct_1(A_471),k9_relat_1(A_471,B_472)) = B_472
      | ~ r1_tarski(B_472,k1_relat_1(A_471))
      | ~ v2_funct_1(A_471)
      | ~ v1_funct_1(A_471)
      | ~ v1_relat_1(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7518,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7127,c_7494])).

tff(c_7527,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_76,c_68,c_6,c_7518])).

tff(c_6795,plain,(
    ! [B_407,A_408] :
      ( k2_relat_1(k7_relat_1(B_407,A_408)) = k9_relat_1(B_407,A_408)
      | ~ v1_relat_1(B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6788,plain,(
    ! [B_404,A_405] :
      ( v5_relat_1(B_404,A_405)
      | ~ r1_tarski(k2_relat_1(B_404),A_405)
      | ~ v1_relat_1(B_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6793,plain,(
    ! [B_404] :
      ( v5_relat_1(B_404,k2_relat_1(B_404))
      | ~ v1_relat_1(B_404) ) ),
    inference(resolution,[status(thm)],[c_6,c_6788])).

tff(c_6801,plain,(
    ! [B_407,A_408] :
      ( v5_relat_1(k7_relat_1(B_407,A_408),k9_relat_1(B_407,A_408))
      | ~ v1_relat_1(k7_relat_1(B_407,A_408))
      | ~ v1_relat_1(B_407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6795,c_6793])).

tff(c_7537,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7527,c_6801])).

tff(c_7693,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7537])).

tff(c_7696,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_7693])).

tff(c_7700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_76,c_68,c_7696])).

tff(c_7702,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7537])).

tff(c_20,plain,(
    ! [A_14] :
      ( v2_funct_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(k2_funct_1(A_15),k9_relat_1(A_15,B_17)) = B_17
      | ~ r1_tarski(B_17,k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7531,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7527,c_26])).

tff(c_8479,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_7661,c_7531])).

tff(c_8480,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8479])).

tff(c_8483,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_8480])).

tff(c_8487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_76,c_68,c_8483])).

tff(c_8489,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8479])).

tff(c_6812,plain,(
    ! [C_410,B_411,A_412] :
      ( v5_relat_1(C_410,B_411)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_412,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6816,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6780,c_6812])).

tff(c_7254,plain,(
    v5_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7246,c_6816])).

tff(c_8703,plain,(
    ! [C_553,B_554,A_555] :
      ( m1_subset_1(k2_funct_1(C_553),k1_zfmisc_1(k2_zfmisc_1(B_554,A_555)))
      | k2_relset_1(A_555,B_554,C_553) != B_554
      | ~ v2_funct_1(C_553)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_555,B_554)))
      | ~ v1_funct_2(C_553,A_555,B_554)
      | ~ v1_funct_1(C_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9355,plain,(
    ! [C_596,B_597,A_598] :
      ( v4_relat_1(k2_funct_1(C_596),B_597)
      | k2_relset_1(A_598,B_597,C_596) != B_597
      | ~ v2_funct_1(C_596)
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(A_598,B_597)))
      | ~ v1_funct_2(C_596,A_598,B_597)
      | ~ v1_funct_1(C_596) ) ),
    inference(resolution,[status(thm)],[c_8703,c_32])).

tff(c_9364,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_9355])).

tff(c_9374,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_68,c_7251,c_9364])).

tff(c_42,plain,(
    ! [B_30,A_29] :
      ( k1_relat_1(B_30) = A_29
      | ~ v1_partfun1(B_30,A_29)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9378,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9374,c_42])).

tff(c_9384,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_9378])).

tff(c_9452,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9384])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9381,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9374,c_18])).

tff(c_9387,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_9381])).

tff(c_9430,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9387,c_16])).

tff(c_9450,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_7527,c_9430])).

tff(c_7169,plain,(
    ! [A_448] :
      ( m1_subset_1(A_448,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_448),k2_relat_1(A_448))))
      | ~ v1_funct_1(A_448)
      | ~ v1_relat_1(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7218,plain,(
    ! [A_449] :
      ( v4_relat_1(A_449,k1_relat_1(A_449))
      | ~ v1_funct_1(A_449)
      | ~ v1_relat_1(A_449) ) ),
    inference(resolution,[status(thm)],[c_7169,c_32])).

tff(c_7296,plain,(
    ! [A_454] :
      ( k7_relat_1(A_454,k1_relat_1(A_454)) = A_454
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454) ) ),
    inference(resolution,[status(thm)],[c_7218,c_18])).

tff(c_7305,plain,(
    ! [A_454] :
      ( k9_relat_1(A_454,k1_relat_1(A_454)) = k2_relat_1(A_454)
      | ~ v1_relat_1(A_454)
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7296,c_16])).

tff(c_7515,plain,(
    ! [A_454] :
      ( k9_relat_1(k2_funct_1(A_454),k2_relat_1(A_454)) = k1_relat_1(A_454)
      | ~ r1_tarski(k1_relat_1(A_454),k1_relat_1(A_454))
      | ~ v2_funct_1(A_454)
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454)
      | ~ v1_relat_1(A_454)
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7305,c_7494])).

tff(c_7525,plain,(
    ! [A_454] :
      ( k9_relat_1(k2_funct_1(A_454),k2_relat_1(A_454)) = k1_relat_1(A_454)
      | ~ v2_funct_1(A_454)
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7515])).

tff(c_9474,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9450,c_7525])).

tff(c_9511,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_7661,c_8489,c_9474])).

tff(c_9957,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9511])).

tff(c_9963,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_76,c_68,c_7127,c_9957])).

tff(c_7953,plain,(
    ! [C_508,B_509,A_510] :
      ( m1_subset_1(k2_funct_1(C_508),k1_zfmisc_1(k2_zfmisc_1(B_509,A_510)))
      | k2_relset_1(A_510,B_509,C_508) != B_509
      | ~ v2_funct_1(C_508)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_510,B_509)))
      | ~ v1_funct_2(C_508,A_510,B_509)
      | ~ v1_funct_1(C_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8193,plain,(
    ! [C_527,B_528,A_529] :
      ( v4_relat_1(k2_funct_1(C_527),B_528)
      | k2_relset_1(A_529,B_528,C_527) != B_528
      | ~ v2_funct_1(C_527)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_529,B_528)))
      | ~ v1_funct_2(C_527,A_529,B_528)
      | ~ v1_funct_1(C_527) ) ),
    inference(resolution,[status(thm)],[c_7953,c_32])).

tff(c_8199,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_8193])).

tff(c_8206,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_68,c_7251,c_8199])).

tff(c_8224,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8206,c_18])).

tff(c_8230,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_8224])).

tff(c_7701,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7537])).

tff(c_7703,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_7701])).

tff(c_8231,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8230,c_7703])).

tff(c_8234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_8231])).

tff(c_8236,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_7701])).

tff(c_8982,plain,(
    ! [C_574,B_575,A_576] :
      ( v4_relat_1(k2_funct_1(C_574),B_575)
      | k2_relset_1(A_576,B_575,C_574) != B_575
      | ~ v2_funct_1(C_574)
      | ~ m1_subset_1(C_574,k1_zfmisc_1(k2_zfmisc_1(A_576,B_575)))
      | ~ v1_funct_2(C_574,A_576,B_575)
      | ~ v1_funct_1(C_574) ) ),
    inference(resolution,[status(thm)],[c_8703,c_32])).

tff(c_8988,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_8982])).

tff(c_8995,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_68,c_7251,c_8988])).

tff(c_9002,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8995,c_18])).

tff(c_9008,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_9002])).

tff(c_8235,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7701])).

tff(c_6822,plain,(
    ! [B_416,A_417] :
      ( r1_tarski(k2_relat_1(B_416),A_417)
      | ~ v5_relat_1(B_416,A_417)
      | ~ v1_relat_1(B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7410,plain,(
    ! [B_464,A_465,A_466] :
      ( r1_tarski(k9_relat_1(B_464,A_465),A_466)
      | ~ v5_relat_1(k7_relat_1(B_464,A_465),A_466)
      | ~ v1_relat_1(k7_relat_1(B_464,A_465))
      | ~ v1_relat_1(B_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6822])).

tff(c_7428,plain,(
    ! [B_464,A_465] :
      ( r1_tarski(k9_relat_1(B_464,A_465),k2_relat_1(k7_relat_1(B_464,A_465)))
      | ~ v1_relat_1(B_464)
      | ~ v1_relat_1(k7_relat_1(B_464,A_465)) ) ),
    inference(resolution,[status(thm)],[c_6793,c_7410])).

tff(c_7534,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7527,c_7428])).

tff(c_8238,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8236,c_7702,c_7534])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6832,plain,(
    ! [B_416,A_417] :
      ( k2_relat_1(B_416) = A_417
      | ~ r1_tarski(A_417,k2_relat_1(B_416))
      | ~ v5_relat_1(B_416,A_417)
      | ~ v1_relat_1(B_416) ) ),
    inference(resolution,[status(thm)],[c_6822,c_2])).

tff(c_8241,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_8238,c_6832])).

tff(c_8249,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8236,c_8241])).

tff(c_8260,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8235,c_8249])).

tff(c_56,plain,(
    ! [A_38] :
      ( v1_funct_2(A_38,k1_relat_1(A_38),k2_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_8289,plain,
    ( v1_funct_2(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8260,c_56])).

tff(c_8324,plain,
    ( v1_funct_2(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8236,c_8289])).

tff(c_8744,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_8324])).

tff(c_9009,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9008,c_8744])).

tff(c_9019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7661,c_9009])).

tff(c_9021,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_8324])).

tff(c_54,plain,(
    ! [A_38] :
      ( m1_subset_1(A_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38),k2_relat_1(A_38))))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_8286,plain,
    ( m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8260,c_54])).

tff(c_8322,plain,
    ( m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8236,c_8286])).

tff(c_9276,plain,(
    m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9021,c_8322])).

tff(c_9326,plain,(
    v4_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_9276,c_32])).

tff(c_40,plain,(
    ! [B_30] :
      ( v1_partfun1(B_30,k1_relat_1(B_30))
      | ~ v4_relat_1(B_30,k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9337,plain,
    ( v1_partfun1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_9326,c_40])).

tff(c_9347,plain,(
    v1_partfun1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8236,c_9337])).

tff(c_9389,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9387,c_9387,c_9347])).

tff(c_9969,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9963,c_9389])).

tff(c_9977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9452,c_9969])).

tff(c_9978,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_9384])).

tff(c_7128,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7125,c_6839])).

tff(c_7419,plain,(
    ! [A_466] :
      ( r1_tarski(k9_relat_1('#skF_3',k1_relat_1('#skF_3')),A_466)
      | ~ v5_relat_1('#skF_3',A_466)
      | ~ v1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7128,c_7410])).

tff(c_7427,plain,(
    ! [A_466] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_466)
      | ~ v5_relat_1('#skF_3',A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_6786,c_7128,c_7127,c_7419])).

tff(c_8488,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_8479])).

tff(c_8490,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_8488])).

tff(c_8497,plain,(
    ~ v5_relat_1('#skF_3',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_7427,c_8490])).

tff(c_10071,plain,(
    ~ v5_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9978,c_8497])).

tff(c_10075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7254,c_10071])).

tff(c_10076,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_8488])).

tff(c_10351,plain,(
    ! [C_621,B_622,A_623] :
      ( m1_subset_1(k2_funct_1(C_621),k1_zfmisc_1(k2_zfmisc_1(B_622,A_623)))
      | k2_relset_1(A_623,B_622,C_621) != B_622
      | ~ v2_funct_1(C_621)
      | ~ m1_subset_1(C_621,k1_zfmisc_1(k2_zfmisc_1(A_623,B_622)))
      | ~ v1_funct_2(C_621,A_623,B_622)
      | ~ v1_funct_1(C_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_11687,plain,(
    ! [C_672,B_673,A_674] :
      ( v4_relat_1(k2_funct_1(C_672),B_673)
      | k2_relset_1(A_674,B_673,C_672) != B_673
      | ~ v2_funct_1(C_672)
      | ~ m1_subset_1(C_672,k1_zfmisc_1(k2_zfmisc_1(A_674,B_673)))
      | ~ v1_funct_2(C_672,A_674,B_673)
      | ~ v1_funct_1(C_672) ) ),
    inference(resolution,[status(thm)],[c_10351,c_32])).

tff(c_11696,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_11687])).

tff(c_11706,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_68,c_7251,c_11696])).

tff(c_11713,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_11706,c_18])).

tff(c_11719,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_11713])).

tff(c_11734,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11719,c_8260])).

tff(c_11812,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11734,c_7525])).

tff(c_11851,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_7661,c_8489,c_10076,c_11812])).

tff(c_10077,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_8488])).

tff(c_10090,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10077,c_2])).

tff(c_10142,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10090])).

tff(c_11869,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11851,c_10142])).

tff(c_11874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11869])).

tff(c_11875,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10090])).

tff(c_11893,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11875,c_7305])).

tff(c_11924,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_7661,c_7702,c_7527,c_11893])).

tff(c_7245,plain,(
    ! [A_38] :
      ( k2_relset_1(k1_relat_1(A_38),k2_relat_1(A_38),A_38) = k2_relat_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_54,c_7237])).

tff(c_11968,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11924,c_7245])).

tff(c_11997,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_7661,c_11924,c_11875,c_11968])).

tff(c_11971,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11924,c_54])).

tff(c_11999,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7702,c_7661,c_11875,c_11971])).

tff(c_64,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_tops_2(A_41,B_42,C_43) = k2_funct_1(C_43)
      | ~ v2_funct_1(C_43)
      | k2_relset_1(A_41,B_42,C_43) != B_42
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_2(C_43,A_41,B_42)
      | ~ v1_funct_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_12174,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_11999,c_64])).

tff(c_12200,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7661,c_8442,c_11997,c_8489,c_12174])).

tff(c_11940,plain,(
    ! [A_675,B_676,C_677] :
      ( k2_tops_2(A_675,B_676,C_677) = k2_funct_1(C_677)
      | ~ v2_funct_1(C_677)
      | k2_relset_1(A_675,B_676,C_677) != B_676
      | ~ m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(A_675,B_676)))
      | ~ v1_funct_2(C_677,A_675,B_676)
      | ~ v1_funct_1(C_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_11943,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7252,c_11940])).

tff(c_11949,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7253,c_7251,c_68,c_11943])).

tff(c_66,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_6811,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_93,c_94,c_94,c_94,c_66])).

tff(c_7130,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7125,c_7125,c_7125,c_6811])).

tff(c_7392,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7246,c_7246,c_7246,c_7130])).

tff(c_12021,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11949,c_7392])).

tff(c_12256,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12200,c_12021])).

tff(c_12263,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_12256])).

tff(c_12266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_76,c_68,c_7650,c_12263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.53/3.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/3.04  
% 8.53/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/3.05  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.53/3.05  
% 8.53/3.05  %Foreground sorts:
% 8.53/3.05  
% 8.53/3.05  
% 8.53/3.05  %Background operators:
% 8.53/3.05  
% 8.53/3.05  
% 8.53/3.05  %Foreground operators:
% 8.53/3.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.53/3.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.53/3.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.53/3.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.53/3.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.53/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.53/3.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.53/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.53/3.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.53/3.05  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.53/3.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.53/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.53/3.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.53/3.05  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.53/3.05  tff('#skF_3', type, '#skF_3': $i).
% 8.53/3.05  tff('#skF_1', type, '#skF_1': $i).
% 8.53/3.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.53/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.53/3.05  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.53/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.53/3.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.53/3.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.53/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.53/3.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.53/3.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.53/3.05  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.53/3.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.53/3.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.53/3.05  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.53/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.53/3.05  
% 8.74/3.08  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.74/3.08  tff(f_207, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 8.74/3.08  tff(f_165, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.74/3.08  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.74/3.08  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.74/3.08  tff(f_173, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.74/3.08  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.74/3.08  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 8.74/3.08  tff(f_111, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.74/3.08  tff(f_135, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.74/3.08  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 8.74/3.08  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.74/3.08  tff(f_68, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 8.74/3.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.74/3.08  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.74/3.08  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.74/3.08  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 8.74/3.08  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.74/3.08  tff(f_161, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 8.74/3.08  tff(f_185, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 8.74/3.08  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.74/3.08  tff(c_78, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_86, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.74/3.08  tff(c_93, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_86])).
% 8.74/3.08  tff(c_82, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_94, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_86])).
% 8.74/3.08  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_6780, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_94, c_72])).
% 8.74/3.08  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.08  tff(c_6783, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6780, c_8])).
% 8.74/3.08  tff(c_6786, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6783])).
% 8.74/3.08  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_6938, plain, (![A_430, B_431, C_432]: (k2_relset_1(A_430, B_431, C_432)=k2_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.74/3.08  tff(c_6946, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6780, c_6938])).
% 8.74/3.08  tff(c_70, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_6767, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_94, c_70])).
% 8.74/3.08  tff(c_6947, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6946, c_6767])).
% 8.74/3.08  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_105, plain, (![A_52]: (~v1_xboole_0(u1_struct_0(A_52)) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.74/3.08  tff(c_111, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_105])).
% 8.74/3.08  tff(c_115, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_111])).
% 8.74/3.08  tff(c_116, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_115])).
% 8.74/3.08  tff(c_6956, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6947, c_116])).
% 8.74/3.08  tff(c_6817, plain, (![C_413, A_414, B_415]: (v4_relat_1(C_413, A_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_414, B_415))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.74/3.08  tff(c_6821, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6780, c_6817])).
% 8.74/3.08  tff(c_6885, plain, (![B_424, A_425]: (k1_relat_1(B_424)=A_425 | ~v1_partfun1(B_424, A_425) | ~v4_relat_1(B_424, A_425) | ~v1_relat_1(B_424))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.74/3.08  tff(c_6888, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6821, c_6885])).
% 8.74/3.08  tff(c_6891, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_6888])).
% 8.74/3.08  tff(c_6892, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_6891])).
% 8.74/3.08  tff(c_74, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_99, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_74])).
% 8.74/3.08  tff(c_100, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_99])).
% 8.74/3.08  tff(c_6957, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6947, c_100])).
% 8.74/3.08  tff(c_6955, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_6947, c_6780])).
% 8.74/3.08  tff(c_7113, plain, (![C_445, A_446, B_447]: (v1_partfun1(C_445, A_446) | ~v1_funct_2(C_445, A_446, B_447) | ~v1_funct_1(C_445) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | v1_xboole_0(B_447))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.74/3.08  tff(c_7116, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6955, c_7113])).
% 8.74/3.08  tff(c_7122, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6957, c_7116])).
% 8.74/3.08  tff(c_7124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6956, c_6892, c_7122])).
% 8.74/3.08  tff(c_7125, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_6891])).
% 8.74/3.08  tff(c_7131, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_7125, c_6780])).
% 8.74/3.08  tff(c_7237, plain, (![A_451, B_452, C_453]: (k2_relset_1(A_451, B_452, C_453)=k2_relat_1(C_453) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(A_451, B_452))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.74/3.08  tff(c_7244, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7131, c_7237])).
% 8.74/3.08  tff(c_7132, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7125, c_6767])).
% 8.74/3.08  tff(c_7246, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7244, c_7132])).
% 8.74/3.08  tff(c_7134, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7125, c_100])).
% 8.74/3.08  tff(c_7253, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7246, c_7134])).
% 8.74/3.08  tff(c_7252, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_7246, c_7131])).
% 8.74/3.08  tff(c_7643, plain, (![A_481, B_482, D_483]: (r2_funct_2(A_481, B_482, D_483, D_483) | ~m1_subset_1(D_483, k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))) | ~v1_funct_2(D_483, A_481, B_482) | ~v1_funct_1(D_483))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.74/3.08  tff(c_7645, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_7643])).
% 8.74/3.08  tff(c_7650, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_7645])).
% 8.74/3.08  tff(c_28, plain, (![A_18]: (k2_funct_1(k2_funct_1(A_18))=A_18 | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.74/3.08  tff(c_7251, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7246, c_7244])).
% 8.74/3.08  tff(c_7652, plain, (![C_484, A_485, B_486]: (v1_funct_1(k2_funct_1(C_484)) | k2_relset_1(A_485, B_486, C_484)!=B_486 | ~v2_funct_1(C_484) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))) | ~v1_funct_2(C_484, A_485, B_486) | ~v1_funct_1(C_484))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.74/3.08  tff(c_7655, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_7652])).
% 8.74/3.08  tff(c_7661, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_68, c_7251, c_7655])).
% 8.74/3.08  tff(c_8433, plain, (![C_537, B_538, A_539]: (v1_funct_2(k2_funct_1(C_537), B_538, A_539) | k2_relset_1(A_539, B_538, C_537)!=B_538 | ~v2_funct_1(C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_539, B_538))) | ~v1_funct_2(C_537, A_539, B_538) | ~v1_funct_1(C_537))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.74/3.08  tff(c_8436, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_8433])).
% 8.74/3.08  tff(c_8442, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_68, c_7251, c_8436])).
% 8.74/3.08  tff(c_24, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.74/3.08  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.74/3.08  tff(c_6833, plain, (![B_418, A_419]: (k7_relat_1(B_418, A_419)=B_418 | ~v4_relat_1(B_418, A_419) | ~v1_relat_1(B_418))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.74/3.08  tff(c_6836, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6821, c_6833])).
% 8.74/3.08  tff(c_6839, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_6836])).
% 8.74/3.08  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.74/3.08  tff(c_6843, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6839, c_16])).
% 8.74/3.08  tff(c_6847, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_6843])).
% 8.74/3.08  tff(c_7127, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7125, c_6847])).
% 8.74/3.08  tff(c_7494, plain, (![A_471, B_472]: (k9_relat_1(k2_funct_1(A_471), k9_relat_1(A_471, B_472))=B_472 | ~r1_tarski(B_472, k1_relat_1(A_471)) | ~v2_funct_1(A_471) | ~v1_funct_1(A_471) | ~v1_relat_1(A_471))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.74/3.08  tff(c_7518, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7127, c_7494])).
% 8.74/3.08  tff(c_7527, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_76, c_68, c_6, c_7518])).
% 8.74/3.08  tff(c_6795, plain, (![B_407, A_408]: (k2_relat_1(k7_relat_1(B_407, A_408))=k9_relat_1(B_407, A_408) | ~v1_relat_1(B_407))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.74/3.08  tff(c_6788, plain, (![B_404, A_405]: (v5_relat_1(B_404, A_405) | ~r1_tarski(k2_relat_1(B_404), A_405) | ~v1_relat_1(B_404))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.74/3.08  tff(c_6793, plain, (![B_404]: (v5_relat_1(B_404, k2_relat_1(B_404)) | ~v1_relat_1(B_404))), inference(resolution, [status(thm)], [c_6, c_6788])).
% 8.74/3.08  tff(c_6801, plain, (![B_407, A_408]: (v5_relat_1(k7_relat_1(B_407, A_408), k9_relat_1(B_407, A_408)) | ~v1_relat_1(k7_relat_1(B_407, A_408)) | ~v1_relat_1(B_407))), inference(superposition, [status(thm), theory('equality')], [c_6795, c_6793])).
% 8.74/3.08  tff(c_7537, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7527, c_6801])).
% 8.74/3.08  tff(c_7693, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7537])).
% 8.74/3.08  tff(c_7696, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_7693])).
% 8.74/3.08  tff(c_7700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6786, c_76, c_68, c_7696])).
% 8.74/3.08  tff(c_7702, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7537])).
% 8.74/3.08  tff(c_20, plain, (![A_14]: (v2_funct_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.74/3.08  tff(c_26, plain, (![A_15, B_17]: (k9_relat_1(k2_funct_1(A_15), k9_relat_1(A_15, B_17))=B_17 | ~r1_tarski(B_17, k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.74/3.08  tff(c_7531, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7527, c_26])).
% 8.74/3.08  tff(c_8479, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_7661, c_7531])).
% 8.74/3.08  tff(c_8480, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8479])).
% 8.74/3.08  tff(c_8483, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_8480])).
% 8.74/3.08  tff(c_8487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6786, c_76, c_68, c_8483])).
% 8.74/3.08  tff(c_8489, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_8479])).
% 8.74/3.08  tff(c_6812, plain, (![C_410, B_411, A_412]: (v5_relat_1(C_410, B_411) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_412, B_411))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.74/3.08  tff(c_6816, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6780, c_6812])).
% 8.74/3.08  tff(c_7254, plain, (v5_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7246, c_6816])).
% 8.74/3.08  tff(c_8703, plain, (![C_553, B_554, A_555]: (m1_subset_1(k2_funct_1(C_553), k1_zfmisc_1(k2_zfmisc_1(B_554, A_555))) | k2_relset_1(A_555, B_554, C_553)!=B_554 | ~v2_funct_1(C_553) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(A_555, B_554))) | ~v1_funct_2(C_553, A_555, B_554) | ~v1_funct_1(C_553))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.74/3.08  tff(c_32, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.74/3.08  tff(c_9355, plain, (![C_596, B_597, A_598]: (v4_relat_1(k2_funct_1(C_596), B_597) | k2_relset_1(A_598, B_597, C_596)!=B_597 | ~v2_funct_1(C_596) | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(A_598, B_597))) | ~v1_funct_2(C_596, A_598, B_597) | ~v1_funct_1(C_596))), inference(resolution, [status(thm)], [c_8703, c_32])).
% 8.74/3.08  tff(c_9364, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_9355])).
% 8.74/3.08  tff(c_9374, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_68, c_7251, c_9364])).
% 8.74/3.08  tff(c_42, plain, (![B_30, A_29]: (k1_relat_1(B_30)=A_29 | ~v1_partfun1(B_30, A_29) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.74/3.08  tff(c_9378, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9374, c_42])).
% 8.74/3.08  tff(c_9384, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_9378])).
% 8.74/3.08  tff(c_9452, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9384])).
% 8.74/3.08  tff(c_18, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.74/3.08  tff(c_9381, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9374, c_18])).
% 8.74/3.08  tff(c_9387, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_9381])).
% 8.74/3.08  tff(c_9430, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9387, c_16])).
% 8.74/3.08  tff(c_9450, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_7527, c_9430])).
% 8.74/3.08  tff(c_7169, plain, (![A_448]: (m1_subset_1(A_448, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_448), k2_relat_1(A_448)))) | ~v1_funct_1(A_448) | ~v1_relat_1(A_448))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.74/3.08  tff(c_7218, plain, (![A_449]: (v4_relat_1(A_449, k1_relat_1(A_449)) | ~v1_funct_1(A_449) | ~v1_relat_1(A_449))), inference(resolution, [status(thm)], [c_7169, c_32])).
% 8.74/3.08  tff(c_7296, plain, (![A_454]: (k7_relat_1(A_454, k1_relat_1(A_454))=A_454 | ~v1_funct_1(A_454) | ~v1_relat_1(A_454))), inference(resolution, [status(thm)], [c_7218, c_18])).
% 8.74/3.08  tff(c_7305, plain, (![A_454]: (k9_relat_1(A_454, k1_relat_1(A_454))=k2_relat_1(A_454) | ~v1_relat_1(A_454) | ~v1_funct_1(A_454) | ~v1_relat_1(A_454))), inference(superposition, [status(thm), theory('equality')], [c_7296, c_16])).
% 8.74/3.08  tff(c_7515, plain, (![A_454]: (k9_relat_1(k2_funct_1(A_454), k2_relat_1(A_454))=k1_relat_1(A_454) | ~r1_tarski(k1_relat_1(A_454), k1_relat_1(A_454)) | ~v2_funct_1(A_454) | ~v1_funct_1(A_454) | ~v1_relat_1(A_454) | ~v1_relat_1(A_454) | ~v1_funct_1(A_454) | ~v1_relat_1(A_454))), inference(superposition, [status(thm), theory('equality')], [c_7305, c_7494])).
% 8.74/3.08  tff(c_7525, plain, (![A_454]: (k9_relat_1(k2_funct_1(A_454), k2_relat_1(A_454))=k1_relat_1(A_454) | ~v2_funct_1(A_454) | ~v1_funct_1(A_454) | ~v1_relat_1(A_454))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7515])).
% 8.74/3.08  tff(c_9474, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9450, c_7525])).
% 8.74/3.08  tff(c_9511, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_7661, c_8489, c_9474])).
% 8.74/3.08  tff(c_9957, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_9511])).
% 8.74/3.08  tff(c_9963, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_76, c_68, c_7127, c_9957])).
% 8.74/3.08  tff(c_7953, plain, (![C_508, B_509, A_510]: (m1_subset_1(k2_funct_1(C_508), k1_zfmisc_1(k2_zfmisc_1(B_509, A_510))) | k2_relset_1(A_510, B_509, C_508)!=B_509 | ~v2_funct_1(C_508) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_510, B_509))) | ~v1_funct_2(C_508, A_510, B_509) | ~v1_funct_1(C_508))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.74/3.08  tff(c_8193, plain, (![C_527, B_528, A_529]: (v4_relat_1(k2_funct_1(C_527), B_528) | k2_relset_1(A_529, B_528, C_527)!=B_528 | ~v2_funct_1(C_527) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_529, B_528))) | ~v1_funct_2(C_527, A_529, B_528) | ~v1_funct_1(C_527))), inference(resolution, [status(thm)], [c_7953, c_32])).
% 8.74/3.08  tff(c_8199, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_8193])).
% 8.74/3.08  tff(c_8206, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_68, c_7251, c_8199])).
% 8.74/3.08  tff(c_8224, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8206, c_18])).
% 8.74/3.08  tff(c_8230, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_8224])).
% 8.74/3.08  tff(c_7701, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7537])).
% 8.74/3.08  tff(c_7703, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_7701])).
% 8.74/3.08  tff(c_8231, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8230, c_7703])).
% 8.74/3.08  tff(c_8234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7702, c_8231])).
% 8.74/3.08  tff(c_8236, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_7701])).
% 8.74/3.08  tff(c_8982, plain, (![C_574, B_575, A_576]: (v4_relat_1(k2_funct_1(C_574), B_575) | k2_relset_1(A_576, B_575, C_574)!=B_575 | ~v2_funct_1(C_574) | ~m1_subset_1(C_574, k1_zfmisc_1(k2_zfmisc_1(A_576, B_575))) | ~v1_funct_2(C_574, A_576, B_575) | ~v1_funct_1(C_574))), inference(resolution, [status(thm)], [c_8703, c_32])).
% 8.74/3.08  tff(c_8988, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_8982])).
% 8.74/3.08  tff(c_8995, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_68, c_7251, c_8988])).
% 8.74/3.08  tff(c_9002, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8995, c_18])).
% 8.74/3.08  tff(c_9008, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_9002])).
% 8.74/3.08  tff(c_8235, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7701])).
% 8.74/3.08  tff(c_6822, plain, (![B_416, A_417]: (r1_tarski(k2_relat_1(B_416), A_417) | ~v5_relat_1(B_416, A_417) | ~v1_relat_1(B_416))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.74/3.08  tff(c_7410, plain, (![B_464, A_465, A_466]: (r1_tarski(k9_relat_1(B_464, A_465), A_466) | ~v5_relat_1(k7_relat_1(B_464, A_465), A_466) | ~v1_relat_1(k7_relat_1(B_464, A_465)) | ~v1_relat_1(B_464))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6822])).
% 8.74/3.08  tff(c_7428, plain, (![B_464, A_465]: (r1_tarski(k9_relat_1(B_464, A_465), k2_relat_1(k7_relat_1(B_464, A_465))) | ~v1_relat_1(B_464) | ~v1_relat_1(k7_relat_1(B_464, A_465)))), inference(resolution, [status(thm)], [c_6793, c_7410])).
% 8.74/3.08  tff(c_7534, plain, (r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7527, c_7428])).
% 8.74/3.08  tff(c_8238, plain, (r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_8236, c_7702, c_7534])).
% 8.74/3.08  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.74/3.08  tff(c_6832, plain, (![B_416, A_417]: (k2_relat_1(B_416)=A_417 | ~r1_tarski(A_417, k2_relat_1(B_416)) | ~v5_relat_1(B_416, A_417) | ~v1_relat_1(B_416))), inference(resolution, [status(thm)], [c_6822, c_2])).
% 8.74/3.08  tff(c_8241, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))=k1_relat_1('#skF_3') | ~v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_8238, c_6832])).
% 8.74/3.08  tff(c_8249, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))=k1_relat_1('#skF_3') | ~v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8236, c_8241])).
% 8.74/3.08  tff(c_8260, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8235, c_8249])).
% 8.74/3.08  tff(c_56, plain, (![A_38]: (v1_funct_2(A_38, k1_relat_1(A_38), k2_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.74/3.08  tff(c_8289, plain, (v1_funct_2(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8260, c_56])).
% 8.74/3.08  tff(c_8324, plain, (v1_funct_2(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8236, c_8289])).
% 8.74/3.08  tff(c_8744, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_8324])).
% 8.74/3.08  tff(c_9009, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9008, c_8744])).
% 8.74/3.08  tff(c_9019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7661, c_9009])).
% 8.74/3.08  tff(c_9021, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_8324])).
% 8.74/3.08  tff(c_54, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38), k2_relat_1(A_38)))) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.74/3.08  tff(c_8286, plain, (m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), k1_relat_1('#skF_3')))) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8260, c_54])).
% 8.74/3.08  tff(c_8322, plain, (m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), k1_relat_1('#skF_3')))) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8236, c_8286])).
% 8.74/3.08  tff(c_9276, plain, (m1_subset_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_9021, c_8322])).
% 8.74/3.08  tff(c_9326, plain, (v4_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(resolution, [status(thm)], [c_9276, c_32])).
% 8.74/3.08  tff(c_40, plain, (![B_30]: (v1_partfun1(B_30, k1_relat_1(B_30)) | ~v4_relat_1(B_30, k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.74/3.08  tff(c_9337, plain, (v1_partfun1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_9326, c_40])).
% 8.74/3.08  tff(c_9347, plain, (v1_partfun1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_8236, c_9337])).
% 8.74/3.08  tff(c_9389, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9387, c_9387, c_9347])).
% 8.74/3.08  tff(c_9969, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9963, c_9389])).
% 8.74/3.08  tff(c_9977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9452, c_9969])).
% 8.74/3.08  tff(c_9978, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_9384])).
% 8.74/3.08  tff(c_7128, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7125, c_6839])).
% 8.74/3.08  tff(c_7419, plain, (![A_466]: (r1_tarski(k9_relat_1('#skF_3', k1_relat_1('#skF_3')), A_466) | ~v5_relat_1('#skF_3', A_466) | ~v1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7128, c_7410])).
% 8.74/3.08  tff(c_7427, plain, (![A_466]: (r1_tarski(k2_relat_1('#skF_3'), A_466) | ~v5_relat_1('#skF_3', A_466))), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_6786, c_7128, c_7127, c_7419])).
% 8.74/3.08  tff(c_8488, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_8479])).
% 8.74/3.08  tff(c_8490, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_8488])).
% 8.74/3.08  tff(c_8497, plain, (~v5_relat_1('#skF_3', k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_7427, c_8490])).
% 8.74/3.08  tff(c_10071, plain, (~v5_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9978, c_8497])).
% 8.74/3.08  tff(c_10075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7254, c_10071])).
% 8.74/3.08  tff(c_10076, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_8488])).
% 8.74/3.08  tff(c_10351, plain, (![C_621, B_622, A_623]: (m1_subset_1(k2_funct_1(C_621), k1_zfmisc_1(k2_zfmisc_1(B_622, A_623))) | k2_relset_1(A_623, B_622, C_621)!=B_622 | ~v2_funct_1(C_621) | ~m1_subset_1(C_621, k1_zfmisc_1(k2_zfmisc_1(A_623, B_622))) | ~v1_funct_2(C_621, A_623, B_622) | ~v1_funct_1(C_621))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.74/3.08  tff(c_11687, plain, (![C_672, B_673, A_674]: (v4_relat_1(k2_funct_1(C_672), B_673) | k2_relset_1(A_674, B_673, C_672)!=B_673 | ~v2_funct_1(C_672) | ~m1_subset_1(C_672, k1_zfmisc_1(k2_zfmisc_1(A_674, B_673))) | ~v1_funct_2(C_672, A_674, B_673) | ~v1_funct_1(C_672))), inference(resolution, [status(thm)], [c_10351, c_32])).
% 8.74/3.08  tff(c_11696, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_11687])).
% 8.74/3.08  tff(c_11706, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_68, c_7251, c_11696])).
% 8.74/3.08  tff(c_11713, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_11706, c_18])).
% 8.74/3.08  tff(c_11719, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_11713])).
% 8.74/3.08  tff(c_11734, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11719, c_8260])).
% 8.74/3.08  tff(c_11812, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11734, c_7525])).
% 8.74/3.08  tff(c_11851, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_7661, c_8489, c_10076, c_11812])).
% 8.74/3.08  tff(c_10077, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_8488])).
% 8.74/3.08  tff(c_10090, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10077, c_2])).
% 8.74/3.08  tff(c_10142, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10090])).
% 8.74/3.08  tff(c_11869, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11851, c_10142])).
% 8.74/3.08  tff(c_11874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_11869])).
% 8.74/3.08  tff(c_11875, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_10090])).
% 8.74/3.08  tff(c_11893, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11875, c_7305])).
% 8.74/3.08  tff(c_11924, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_7661, c_7702, c_7527, c_11893])).
% 8.74/3.08  tff(c_7245, plain, (![A_38]: (k2_relset_1(k1_relat_1(A_38), k2_relat_1(A_38), A_38)=k2_relat_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_54, c_7237])).
% 8.74/3.08  tff(c_11968, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11924, c_7245])).
% 8.74/3.08  tff(c_11997, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_7661, c_11924, c_11875, c_11968])).
% 8.74/3.08  tff(c_11971, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11924, c_54])).
% 8.74/3.08  tff(c_11999, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_7702, c_7661, c_11875, c_11971])).
% 8.74/3.08  tff(c_64, plain, (![A_41, B_42, C_43]: (k2_tops_2(A_41, B_42, C_43)=k2_funct_1(C_43) | ~v2_funct_1(C_43) | k2_relset_1(A_41, B_42, C_43)!=B_42 | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_2(C_43, A_41, B_42) | ~v1_funct_1(C_43))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.74/3.08  tff(c_12174, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_11999, c_64])).
% 8.74/3.08  tff(c_12200, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7661, c_8442, c_11997, c_8489, c_12174])).
% 8.74/3.08  tff(c_11940, plain, (![A_675, B_676, C_677]: (k2_tops_2(A_675, B_676, C_677)=k2_funct_1(C_677) | ~v2_funct_1(C_677) | k2_relset_1(A_675, B_676, C_677)!=B_676 | ~m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(A_675, B_676))) | ~v1_funct_2(C_677, A_675, B_676) | ~v1_funct_1(C_677))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.74/3.08  tff(c_11943, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7252, c_11940])).
% 8.74/3.08  tff(c_11949, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7253, c_7251, c_68, c_11943])).
% 8.74/3.08  tff(c_66, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 8.74/3.08  tff(c_6811, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_93, c_94, c_94, c_94, c_66])).
% 8.74/3.08  tff(c_7130, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7125, c_7125, c_7125, c_6811])).
% 8.74/3.08  tff(c_7392, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7246, c_7246, c_7246, c_7130])).
% 8.74/3.08  tff(c_12021, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11949, c_7392])).
% 8.74/3.08  tff(c_12256, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12200, c_12021])).
% 8.74/3.08  tff(c_12263, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_12256])).
% 8.74/3.08  tff(c_12266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6786, c_76, c_68, c_7650, c_12263])).
% 8.74/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.74/3.08  
% 8.74/3.08  Inference rules
% 8.74/3.08  ----------------------
% 8.74/3.08  #Ref     : 0
% 8.74/3.08  #Sup     : 2556
% 8.74/3.08  #Fact    : 0
% 8.74/3.08  #Define  : 0
% 8.74/3.08  #Split   : 39
% 8.74/3.08  #Chain   : 0
% 8.74/3.08  #Close   : 0
% 8.74/3.08  
% 8.74/3.08  Ordering : KBO
% 8.74/3.08  
% 8.74/3.08  Simplification rules
% 8.74/3.08  ----------------------
% 8.74/3.08  #Subsume      : 430
% 8.74/3.08  #Demod        : 5384
% 8.74/3.08  #Tautology    : 976
% 8.74/3.08  #SimpNegUnit  : 15
% 8.74/3.08  #BackRed      : 220
% 8.74/3.08  
% 8.74/3.08  #Partial instantiations: 0
% 8.74/3.08  #Strategies tried      : 1
% 8.74/3.08  
% 8.74/3.08  Timing (in seconds)
% 8.74/3.08  ----------------------
% 8.74/3.08  Preprocessing        : 0.37
% 8.74/3.08  Parsing              : 0.20
% 8.74/3.08  CNF conversion       : 0.03
% 8.74/3.08  Main loop            : 1.90
% 8.74/3.08  Inferencing          : 0.61
% 8.74/3.08  Reduction            : 0.71
% 8.74/3.08  Demodulation         : 0.53
% 8.74/3.08  BG Simplification    : 0.07
% 8.74/3.08  Subsumption          : 0.36
% 8.74/3.08  Abstraction          : 0.09
% 8.74/3.08  MUC search           : 0.00
% 8.74/3.08  Cooper               : 0.00
% 8.74/3.08  Total                : 2.34
% 8.74/3.08  Index Insertion      : 0.00
% 8.74/3.08  Index Deletion       : 0.00
% 8.74/3.08  Index Matching       : 0.00
% 8.74/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
