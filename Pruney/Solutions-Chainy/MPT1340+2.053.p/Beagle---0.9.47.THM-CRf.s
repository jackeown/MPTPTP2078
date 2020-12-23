%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:37 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  141 (3889 expanded)
%              Number of leaves         :   49 (1391 expanded)
%              Depth                    :   18
%              Number of atoms          :  286 (11212 expanded)
%              Number of equality atoms :   63 (2580 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_196,negated_conjecture,(
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

tff(f_136,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_116,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_132,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_174,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_70,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_78,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_70])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_77,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_70])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_95,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_58])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_149,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_153,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_149])).

tff(c_56,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_89,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_56])).

tff(c_154,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_89])).

tff(c_46,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(k2_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_168,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_46])).

tff(c_172,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_168])).

tff(c_173,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_172])).

tff(c_107,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_95,c_107])).

tff(c_142,plain,(
    ! [B_70,A_71] :
      ( k1_relat_1(B_70) = A_71
      | ~ v1_partfun1(B_70,A_71)
      | ~ v4_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_145,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_142])).

tff(c_148,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_145])).

tff(c_203,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_87,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_60])).

tff(c_163,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_87])).

tff(c_162,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_95])).

tff(c_499,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_partfun1(C_102,A_103)
      | ~ v1_funct_2(C_102,A_103,B_104)
      | ~ v1_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | v1_xboole_0(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_511,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_162,c_499])).

tff(c_520,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_163,c_511])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_203,c_520])).

tff(c_523,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_527,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_163])).

tff(c_526,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_162])).

tff(c_3068,plain,(
    ! [A_246,B_247,D_248] :
      ( r2_funct_2(A_246,B_247,D_248,D_248)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_2(D_248,A_246,B_247)
      | ~ v1_funct_1(D_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3076,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_3068])).

tff(c_3084,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_527,c_3076])).

tff(c_8,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_191,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_18])).

tff(c_558,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_191])).

tff(c_4578,plain,(
    ! [C_322,A_323,B_324] :
      ( v1_funct_1(k2_funct_1(C_322))
      | k2_relset_1(A_323,B_324,C_322) != B_324
      | ~ v2_funct_1(C_322)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324)))
      | ~ v1_funct_2(C_322,A_323,B_324)
      | ~ v1_funct_1(C_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4593,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_4578])).

tff(c_4604,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_527,c_54,c_558,c_4593])).

tff(c_5664,plain,(
    ! [C_380,B_381,A_382] :
      ( v1_funct_2(k2_funct_1(C_380),B_381,A_382)
      | k2_relset_1(A_382,B_381,C_380) != B_381
      | ~ v2_funct_1(C_380)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_382,B_381)))
      | ~ v1_funct_2(C_380,A_382,B_381)
      | ~ v1_funct_1(C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5679,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_5664])).

tff(c_5690,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_527,c_54,c_558,c_5679])).

tff(c_595,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_599,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_595])).

tff(c_113,plain,(
    ! [A_67] :
      ( k4_relat_1(A_67) = k2_funct_1(A_67)
      | ~ v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_116,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_113])).

tff(c_119,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_62,c_116])).

tff(c_584,plain,(
    ! [A_105,B_106,C_107] :
      ( k3_relset_1(A_105,B_106,C_107) = k4_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_587,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_584])).

tff(c_589,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_587])).

tff(c_669,plain,(
    ! [B_114,A_115,C_116] :
      ( k2_relset_1(B_114,A_115,k3_relset_1(A_115,B_114,C_116)) = k1_relset_1(A_115,B_114,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_675,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_669])).

tff(c_679,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_589,c_675])).

tff(c_605,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1(k3_relset_1(A_111,B_112,C_113),k1_zfmisc_1(k2_zfmisc_1(B_112,A_111)))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_626,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_605])).

tff(c_636,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_626])).

tff(c_5715,plain,(
    ! [A_383,B_384,C_385] :
      ( k2_tops_2(A_383,B_384,C_385) = k2_funct_1(C_385)
      | ~ v2_funct_1(C_385)
      | k2_relset_1(A_383,B_384,C_385) != B_384
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384)))
      | ~ v1_funct_2(C_385,A_383,B_384)
      | ~ v1_funct_1(C_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_5721,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_636,c_5715])).

tff(c_5733,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4604,c_5690,c_679,c_5721])).

tff(c_5922,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5733])).

tff(c_5727,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_5715])).

tff(c_5737,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_527,c_558,c_54,c_5727])).

tff(c_529,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_78])).

tff(c_164,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_77])).

tff(c_6111,plain,(
    ! [A_400,B_401,C_402] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_400),u1_struct_0(B_401),C_402))
      | ~ v2_funct_1(C_402)
      | k2_relset_1(u1_struct_0(A_400),u1_struct_0(B_401),C_402) != k2_struct_0(B_401)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_400),u1_struct_0(B_401))))
      | ~ v1_funct_2(C_402,u1_struct_0(A_400),u1_struct_0(B_401))
      | ~ v1_funct_1(C_402)
      | ~ l1_struct_0(B_401)
      | ~ l1_struct_0(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_6131,plain,(
    ! [A_400,C_402] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_400),u1_struct_0('#skF_2'),C_402))
      | ~ v2_funct_1(C_402)
      | k2_relset_1(u1_struct_0(A_400),u1_struct_0('#skF_2'),C_402) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_400),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_402,u1_struct_0(A_400),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_402)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_400) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_6111])).

tff(c_6226,plain,(
    ! [A_412,C_413] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_412),k2_relat_1('#skF_3'),C_413))
      | ~ v2_funct_1(C_413)
      | k2_relset_1(u1_struct_0(A_412),k2_relat_1('#skF_3'),C_413) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_413,u1_struct_0(A_412),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_413)
      | ~ l1_struct_0(A_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_164,c_154,c_164,c_164,c_6131])).

tff(c_6237,plain,(
    ! [C_413] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_413))
      | ~ v2_funct_1(C_413)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_413) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_413,u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_413)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_6226])).

tff(c_6460,plain,(
    ! [C_424] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_424))
      | ~ v2_funct_1(C_424)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_424) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_424,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_424) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_529,c_529,c_529,c_6237])).

tff(c_6477,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_6460])).

tff(c_6487,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_527,c_558,c_54,c_5737,c_6477])).

tff(c_6489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5922,c_6487])).

tff(c_6490,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5733])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_112,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_78,c_77,c_77,c_77,c_52])).

tff(c_160,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_154,c_154,c_112])).

tff(c_600,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_523,c_523,c_160])).

tff(c_5738,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5737,c_600])).

tff(c_6767,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6490,c_5738])).

tff(c_6774,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_6767])).

tff(c_6777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_62,c_54,c_3084,c_6774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:48:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.02/2.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/2.77  
% 8.02/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/2.78  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.02/2.78  
% 8.02/2.78  %Foreground sorts:
% 8.02/2.78  
% 8.02/2.78  
% 8.02/2.78  %Background operators:
% 8.02/2.78  
% 8.02/2.78  
% 8.02/2.78  %Foreground operators:
% 8.02/2.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.02/2.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.02/2.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.02/2.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.02/2.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.02/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.02/2.78  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 8.02/2.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.02/2.78  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.02/2.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.02/2.78  tff('#skF_2', type, '#skF_2': $i).
% 8.02/2.78  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.02/2.78  tff('#skF_3', type, '#skF_3': $i).
% 8.02/2.78  tff('#skF_1', type, '#skF_1': $i).
% 8.02/2.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.02/2.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.02/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.02/2.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.02/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.02/2.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.02/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.02/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.02/2.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.02/2.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.02/2.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.02/2.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.02/2.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.02/2.78  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.02/2.78  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.02/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.02/2.78  
% 8.02/2.80  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.02/2.80  tff(f_196, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 8.02/2.80  tff(f_136, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 8.02/2.80  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.02/2.80  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.02/2.80  tff(f_144, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 8.02/2.80  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.02/2.80  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 8.02/2.80  tff(f_92, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.02/2.80  tff(f_116, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.02/2.80  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 8.02/2.80  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.02/2.80  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.02/2.80  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.02/2.80  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 8.02/2.80  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 8.02/2.80  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 8.02/2.80  tff(f_156, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 8.02/2.80  tff(f_174, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 8.02/2.80  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.02/2.80  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_70, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.02/2.80  tff(c_78, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_70])).
% 8.02/2.80  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_77, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_70])).
% 8.02/2.80  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_95, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_58])).
% 8.02/2.80  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.02/2.80  tff(c_98, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_95, c_2])).
% 8.02/2.80  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_98])).
% 8.02/2.80  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_149, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.02/2.80  tff(c_153, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_95, c_149])).
% 8.02/2.80  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_89, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_56])).
% 8.02/2.80  tff(c_154, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_89])).
% 8.02/2.80  tff(c_46, plain, (![A_40]: (~v1_xboole_0(k2_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.02/2.80  tff(c_168, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_46])).
% 8.02/2.80  tff(c_172, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_168])).
% 8.02/2.80  tff(c_173, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_172])).
% 8.02/2.80  tff(c_107, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.80  tff(c_111, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_95, c_107])).
% 8.02/2.80  tff(c_142, plain, (![B_70, A_71]: (k1_relat_1(B_70)=A_71 | ~v1_partfun1(B_70, A_71) | ~v4_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.02/2.80  tff(c_145, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_111, c_142])).
% 8.02/2.80  tff(c_148, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_145])).
% 8.02/2.80  tff(c_203, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_148])).
% 8.02/2.80  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_87, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_60])).
% 8.02/2.80  tff(c_163, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_87])).
% 8.02/2.80  tff(c_162, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_95])).
% 8.02/2.80  tff(c_499, plain, (![C_102, A_103, B_104]: (v1_partfun1(C_102, A_103) | ~v1_funct_2(C_102, A_103, B_104) | ~v1_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | v1_xboole_0(B_104))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.02/2.80  tff(c_511, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_162, c_499])).
% 8.02/2.80  tff(c_520, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_163, c_511])).
% 8.02/2.80  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_203, c_520])).
% 8.02/2.80  tff(c_523, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 8.02/2.80  tff(c_527, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_163])).
% 8.02/2.80  tff(c_526, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_162])).
% 8.02/2.80  tff(c_3068, plain, (![A_246, B_247, D_248]: (r2_funct_2(A_246, B_247, D_248, D_248) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~v1_funct_2(D_248, A_246, B_247) | ~v1_funct_1(D_248))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.02/2.80  tff(c_3076, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_3068])).
% 8.02/2.80  tff(c_3084, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_527, c_3076])).
% 8.02/2.80  tff(c_8, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.02/2.80  tff(c_18, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.02/2.80  tff(c_191, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_162, c_18])).
% 8.02/2.80  tff(c_558, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_191])).
% 8.02/2.80  tff(c_4578, plain, (![C_322, A_323, B_324]: (v1_funct_1(k2_funct_1(C_322)) | k2_relset_1(A_323, B_324, C_322)!=B_324 | ~v2_funct_1(C_322) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))) | ~v1_funct_2(C_322, A_323, B_324) | ~v1_funct_1(C_322))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.02/2.80  tff(c_4593, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_4578])).
% 8.02/2.80  tff(c_4604, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_527, c_54, c_558, c_4593])).
% 8.02/2.80  tff(c_5664, plain, (![C_380, B_381, A_382]: (v1_funct_2(k2_funct_1(C_380), B_381, A_382) | k2_relset_1(A_382, B_381, C_380)!=B_381 | ~v2_funct_1(C_380) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_382, B_381))) | ~v1_funct_2(C_380, A_382, B_381) | ~v1_funct_1(C_380))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.02/2.80  tff(c_5679, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_5664])).
% 8.02/2.80  tff(c_5690, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_527, c_54, c_558, c_5679])).
% 8.02/2.80  tff(c_595, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.02/2.80  tff(c_599, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_595])).
% 8.02/2.80  tff(c_113, plain, (![A_67]: (k4_relat_1(A_67)=k2_funct_1(A_67) | ~v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.02/2.80  tff(c_116, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_113])).
% 8.02/2.80  tff(c_119, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_62, c_116])).
% 8.02/2.80  tff(c_584, plain, (![A_105, B_106, C_107]: (k3_relset_1(A_105, B_106, C_107)=k4_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.02/2.80  tff(c_587, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_584])).
% 8.02/2.80  tff(c_589, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_587])).
% 8.02/2.80  tff(c_669, plain, (![B_114, A_115, C_116]: (k2_relset_1(B_114, A_115, k3_relset_1(A_115, B_114, C_116))=k1_relset_1(A_115, B_114, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.02/2.80  tff(c_675, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_526, c_669])).
% 8.02/2.80  tff(c_679, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_589, c_675])).
% 8.02/2.80  tff(c_605, plain, (![A_111, B_112, C_113]: (m1_subset_1(k3_relset_1(A_111, B_112, C_113), k1_zfmisc_1(k2_zfmisc_1(B_112, A_111))) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.02/2.80  tff(c_626, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_589, c_605])).
% 8.02/2.80  tff(c_636, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_626])).
% 8.02/2.80  tff(c_5715, plain, (![A_383, B_384, C_385]: (k2_tops_2(A_383, B_384, C_385)=k2_funct_1(C_385) | ~v2_funct_1(C_385) | k2_relset_1(A_383, B_384, C_385)!=B_384 | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))) | ~v1_funct_2(C_385, A_383, B_384) | ~v1_funct_1(C_385))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.02/2.80  tff(c_5721, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_636, c_5715])).
% 8.02/2.80  tff(c_5733, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4604, c_5690, c_679, c_5721])).
% 8.02/2.80  tff(c_5922, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5733])).
% 8.02/2.80  tff(c_5727, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_5715])).
% 8.02/2.80  tff(c_5737, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_527, c_558, c_54, c_5727])).
% 8.02/2.80  tff(c_529, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_78])).
% 8.02/2.80  tff(c_164, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_77])).
% 8.02/2.80  tff(c_6111, plain, (![A_400, B_401, C_402]: (v2_funct_1(k2_tops_2(u1_struct_0(A_400), u1_struct_0(B_401), C_402)) | ~v2_funct_1(C_402) | k2_relset_1(u1_struct_0(A_400), u1_struct_0(B_401), C_402)!=k2_struct_0(B_401) | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_400), u1_struct_0(B_401)))) | ~v1_funct_2(C_402, u1_struct_0(A_400), u1_struct_0(B_401)) | ~v1_funct_1(C_402) | ~l1_struct_0(B_401) | ~l1_struct_0(A_400))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.02/2.80  tff(c_6131, plain, (![A_400, C_402]: (v2_funct_1(k2_tops_2(u1_struct_0(A_400), u1_struct_0('#skF_2'), C_402)) | ~v2_funct_1(C_402) | k2_relset_1(u1_struct_0(A_400), u1_struct_0('#skF_2'), C_402)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_400), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_402, u1_struct_0(A_400), u1_struct_0('#skF_2')) | ~v1_funct_1(C_402) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_400))), inference(superposition, [status(thm), theory('equality')], [c_164, c_6111])).
% 8.02/2.80  tff(c_6226, plain, (![A_412, C_413]: (v2_funct_1(k2_tops_2(u1_struct_0(A_412), k2_relat_1('#skF_3'), C_413)) | ~v2_funct_1(C_413) | k2_relset_1(u1_struct_0(A_412), k2_relat_1('#skF_3'), C_413)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_413, u1_struct_0(A_412), k2_relat_1('#skF_3')) | ~v1_funct_1(C_413) | ~l1_struct_0(A_412))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_164, c_154, c_164, c_164, c_6131])).
% 8.02/2.80  tff(c_6237, plain, (![C_413]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_413)) | ~v2_funct_1(C_413) | k2_relset_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_413)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_413, u1_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_413) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_529, c_6226])).
% 8.02/2.80  tff(c_6460, plain, (![C_424]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_424)) | ~v2_funct_1(C_424) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_424)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_424, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_424))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_529, c_529, c_529, c_6237])).
% 8.02/2.80  tff(c_6477, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_6460])).
% 8.02/2.80  tff(c_6487, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_527, c_558, c_54, c_5737, c_6477])).
% 8.02/2.80  tff(c_6489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5922, c_6487])).
% 8.02/2.80  tff(c_6490, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5733])).
% 8.02/2.80  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.02/2.80  tff(c_112, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_78, c_77, c_77, c_77, c_52])).
% 8.02/2.80  tff(c_160, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_154, c_154, c_112])).
% 8.02/2.80  tff(c_600, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_523, c_523, c_160])).
% 8.02/2.80  tff(c_5738, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5737, c_600])).
% 8.02/2.80  tff(c_6767, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6490, c_5738])).
% 8.02/2.80  tff(c_6774, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_6767])).
% 8.02/2.80  tff(c_6777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_62, c_54, c_3084, c_6774])).
% 8.02/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/2.80  
% 8.02/2.80  Inference rules
% 8.02/2.80  ----------------------
% 8.02/2.80  #Ref     : 0
% 8.02/2.80  #Sup     : 1526
% 8.02/2.80  #Fact    : 0
% 8.02/2.80  #Define  : 0
% 8.02/2.80  #Split   : 44
% 8.02/2.80  #Chain   : 0
% 8.02/2.80  #Close   : 0
% 8.02/2.80  
% 8.02/2.80  Ordering : KBO
% 8.02/2.80  
% 8.02/2.80  Simplification rules
% 8.02/2.80  ----------------------
% 8.02/2.80  #Subsume      : 85
% 8.02/2.80  #Demod        : 1950
% 8.02/2.80  #Tautology    : 651
% 8.02/2.80  #SimpNegUnit  : 42
% 8.02/2.80  #BackRed      : 193
% 8.02/2.80  
% 8.02/2.80  #Partial instantiations: 0
% 8.02/2.80  #Strategies tried      : 1
% 8.02/2.80  
% 8.02/2.80  Timing (in seconds)
% 8.02/2.80  ----------------------
% 8.02/2.81  Preprocessing        : 0.36
% 8.02/2.81  Parsing              : 0.19
% 8.02/2.81  CNF conversion       : 0.02
% 8.02/2.81  Main loop            : 1.62
% 8.02/2.81  Inferencing          : 0.48
% 8.02/2.82  Reduction            : 0.65
% 8.02/2.82  Demodulation         : 0.49
% 8.02/2.82  BG Simplification    : 0.05
% 8.02/2.82  Subsumption          : 0.31
% 8.02/2.82  Abstraction          : 0.08
% 8.39/2.82  MUC search           : 0.00
% 8.39/2.82  Cooper               : 0.00
% 8.39/2.82  Total                : 2.03
% 8.39/2.82  Index Insertion      : 0.00
% 8.39/2.82  Index Deletion       : 0.00
% 8.39/2.82  Index Matching       : 0.00
% 8.39/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
