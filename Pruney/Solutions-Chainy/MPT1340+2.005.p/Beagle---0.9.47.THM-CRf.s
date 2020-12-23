%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:30 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :  158 (9587 expanded)
%              Number of leaves         :   48 (3348 expanded)
%              Depth                    :   24
%              Number of atoms          :  321 (27594 expanded)
%              Number of equality atoms :   72 (6241 expanded)
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

tff(f_191,negated_conjecture,(
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

tff(f_131,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_111,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_127,axiom,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_169,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_67,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_67])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_74,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_67])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_56])).

tff(c_6,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_6])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_155,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_155])).

tff(c_54,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_85,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_54])).

tff(c_160,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_85])).

tff(c_44,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(k2_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_175,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_44])).

tff(c_179,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_175])).

tff(c_180,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_179])).

tff(c_103,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_93,c_103])).

tff(c_138,plain,(
    ! [B_67,A_68] :
      ( k1_relat_1(B_67) = A_68
      | ~ v1_partfun1(B_67,A_68)
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_141,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_138])).

tff(c_144,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_141])).

tff(c_154,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_58])).

tff(c_90,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_76])).

tff(c_170,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_90])).

tff(c_169,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_93])).

tff(c_327,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_partfun1(C_84,A_85)
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | v1_xboole_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_336,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_169,c_327])).

tff(c_342,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_170,c_336])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_154,c_342])).

tff(c_345,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_350,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_93])).

tff(c_405,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_409,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_350,c_405])).

tff(c_352,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_85])).

tff(c_414,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_352])).

tff(c_351,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_90])).

tff(c_422,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_351])).

tff(c_421,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_350])).

tff(c_2593,plain,(
    ! [A_211,B_212,D_213] :
      ( r2_funct_2(A_211,B_212,D_213,D_213)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212)))
      | ~ v1_funct_2(D_213,A_211,B_212)
      | ~ v1_funct_1(D_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2601,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_2593])).

tff(c_2609,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_422,c_2601])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,(
    ! [A_66] :
      ( k4_relat_1(A_66) = k2_funct_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_127])).

tff(c_133,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_130])).

tff(c_466,plain,(
    ! [A_90,B_91,C_92] :
      ( k3_relset_1(A_90,B_91,C_92) = k4_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_469,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_466])).

tff(c_471,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_469])).

tff(c_485,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1(k3_relset_1(A_93,B_94,C_95),k1_zfmisc_1(k2_zfmisc_1(B_94,A_93)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_506,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_485])).

tff(c_514,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_506])).

tff(c_2605,plain,
    ( r2_funct_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'),k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_514,c_2593])).

tff(c_6046,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2605])).

tff(c_419,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_409])).

tff(c_6105,plain,(
    ! [C_389,A_390,B_391] :
      ( v1_funct_1(k2_funct_1(C_389))
      | k2_relset_1(A_390,B_391,C_389) != B_391
      | ~ v2_funct_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391)))
      | ~ v1_funct_2(C_389,A_390,B_391)
      | ~ v1_funct_1(C_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6120,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_6105])).

tff(c_6131,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_422,c_52,c_419,c_6120])).

tff(c_6133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6046,c_6131])).

tff(c_6135,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2605])).

tff(c_6134,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | r2_funct_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'),k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2605])).

tff(c_6142,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6134])).

tff(c_6252,plain,(
    ! [C_398,B_399,A_400] :
      ( v1_funct_2(k2_funct_1(C_398),B_399,A_400)
      | k2_relset_1(A_400,B_399,C_398) != B_399
      | ~ v2_funct_1(C_398)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_400,B_399)))
      | ~ v1_funct_2(C_398,A_400,B_399)
      | ~ v1_funct_1(C_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6267,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_6252])).

tff(c_6278,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_422,c_52,c_419,c_6267])).

tff(c_6280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6142,c_6278])).

tff(c_6282,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6134])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_398,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_350,c_14])).

tff(c_472,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_398])).

tff(c_539,plain,(
    ! [B_96,A_97,C_98] :
      ( k2_relset_1(B_96,A_97,k3_relset_1(A_97,B_96,C_98)) = k1_relset_1(A_97,B_96,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_545,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_539])).

tff(c_549,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_472,c_545])).

tff(c_6348,plain,(
    ! [C_401,A_402,B_403] :
      ( v1_funct_1(k2_funct_1(C_401))
      | k2_relset_1(A_402,B_403,C_401) != B_403
      | ~ v2_funct_1(C_401)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_2(C_401,A_402,B_403)
      | ~ v1_funct_1(C_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6357,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_514,c_6348])).

tff(c_6372,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6135,c_6282,c_549,c_6357])).

tff(c_6377,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6372])).

tff(c_6597,plain,(
    ! [A_413,B_414,C_415] :
      ( k2_tops_2(A_413,B_414,C_415) = k2_funct_1(C_415)
      | ~ v2_funct_1(C_415)
      | k2_relset_1(A_413,B_414,C_415) != B_414
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414)))
      | ~ v1_funct_2(C_415,A_413,B_414)
      | ~ v1_funct_1(C_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_6615,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_6597])).

tff(c_6629,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_422,c_419,c_52,c_6615])).

tff(c_424,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_74])).

tff(c_353,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_75])).

tff(c_7130,plain,(
    ! [A_439,B_440,C_441] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_439),u1_struct_0(B_440),C_441))
      | ~ v2_funct_1(C_441)
      | k2_relset_1(u1_struct_0(A_439),u1_struct_0(B_440),C_441) != k2_struct_0(B_440)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_439),u1_struct_0(B_440))))
      | ~ v1_funct_2(C_441,u1_struct_0(A_439),u1_struct_0(B_440))
      | ~ v1_funct_1(C_441)
      | ~ l1_struct_0(B_440)
      | ~ l1_struct_0(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_7147,plain,(
    ! [B_440,C_441] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_440),C_441))
      | ~ v2_funct_1(C_441)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_440),C_441) != k2_struct_0(B_440)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_440))))
      | ~ v1_funct_2(C_441,u1_struct_0('#skF_1'),u1_struct_0(B_440))
      | ~ v1_funct_1(C_441)
      | ~ l1_struct_0(B_440)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_7130])).

tff(c_7222,plain,(
    ! [B_448,C_449] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0(B_448),C_449))
      | ~ v2_funct_1(C_449)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0(B_448),C_449) != k2_struct_0(B_448)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_448))))
      | ~ v1_funct_2(C_449,k1_relat_1('#skF_3'),u1_struct_0(B_448))
      | ~ v1_funct_1(C_449)
      | ~ l1_struct_0(B_448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_353,c_353,c_353,c_7147])).

tff(c_7233,plain,(
    ! [C_449] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_449))
      | ~ v2_funct_1(C_449)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_449) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_449,k1_relat_1('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_449)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_7222])).

tff(c_7358,plain,(
    ! [C_456] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_456))
      | ~ v2_funct_1(C_456)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_456) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_456,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_424,c_414,c_424,c_424,c_7233])).

tff(c_7375,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_7358])).

tff(c_7385,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_422,c_419,c_52,c_6629,c_7375])).

tff(c_7387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6377,c_7385])).

tff(c_7389,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6372])).

tff(c_7530,plain,(
    ! [A_460,B_461,C_462] :
      ( k2_tops_2(A_460,B_461,C_462) = k2_funct_1(C_462)
      | ~ v2_funct_1(C_462)
      | k2_relset_1(A_460,B_461,C_462) != B_461
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | ~ v1_funct_2(C_462,A_460,B_461)
      | ~ v1_funct_1(C_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_7533,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_514,c_7530])).

tff(c_7542,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6135,c_6282,c_549,c_7389,c_7533])).

tff(c_7539,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_7530])).

tff(c_7546,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_422,c_419,c_52,c_7539])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_108,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_75,c_74,c_74,c_74,c_50])).

tff(c_348,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_345,c_345,c_108])).

tff(c_482,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_414,c_414,c_348])).

tff(c_7547,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7546,c_482])).

tff(c_7720,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7542,c_7547])).

tff(c_7727,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7720])).

tff(c_7730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_52,c_2609,c_7727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.07/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/2.82  
% 8.07/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/2.82  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.07/2.82  
% 8.07/2.82  %Foreground sorts:
% 8.07/2.82  
% 8.07/2.82  
% 8.07/2.82  %Background operators:
% 8.07/2.82  
% 8.07/2.82  
% 8.07/2.82  %Foreground operators:
% 8.07/2.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.07/2.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.07/2.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.07/2.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.07/2.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.07/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.07/2.82  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 8.07/2.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.07/2.82  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.07/2.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.07/2.82  tff('#skF_2', type, '#skF_2': $i).
% 8.07/2.82  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.07/2.82  tff('#skF_3', type, '#skF_3': $i).
% 8.07/2.82  tff('#skF_1', type, '#skF_1': $i).
% 8.07/2.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.07/2.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.07/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.07/2.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.07/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.07/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.07/2.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.07/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.07/2.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.07/2.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.07/2.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.07/2.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.07/2.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.07/2.82  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.07/2.82  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.07/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.07/2.82  
% 8.19/2.85  tff(f_191, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 8.19/2.85  tff(f_131, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.19/2.85  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.19/2.85  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.19/2.85  tff(f_139, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 8.19/2.85  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.19/2.85  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 8.19/2.85  tff(f_87, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.19/2.85  tff(f_111, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.19/2.85  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 8.19/2.85  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 8.19/2.85  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 8.19/2.85  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 8.19/2.85  tff(f_127, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.19/2.85  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.19/2.85  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relset_1)).
% 8.19/2.85  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 8.19/2.85  tff(f_169, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 8.19/2.85  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_67, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.19/2.85  tff(c_75, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_67])).
% 8.19/2.85  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_74, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_67])).
% 8.19/2.85  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_56])).
% 8.19/2.85  tff(c_6, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.19/2.85  tff(c_97, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_6])).
% 8.19/2.85  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_155, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.19/2.85  tff(c_159, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_155])).
% 8.19/2.85  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_85, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_54])).
% 8.19/2.85  tff(c_160, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_85])).
% 8.19/2.85  tff(c_44, plain, (![A_38]: (~v1_xboole_0(k2_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.19/2.85  tff(c_175, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_160, c_44])).
% 8.19/2.85  tff(c_179, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_175])).
% 8.19/2.85  tff(c_180, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_179])).
% 8.19/2.85  tff(c_103, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.19/2.85  tff(c_107, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_93, c_103])).
% 8.19/2.85  tff(c_138, plain, (![B_67, A_68]: (k1_relat_1(B_67)=A_68 | ~v1_partfun1(B_67, A_68) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.19/2.85  tff(c_141, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_107, c_138])).
% 8.19/2.85  tff(c_144, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_141])).
% 8.19/2.85  tff(c_154, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_144])).
% 8.19/2.85  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_76, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_58])).
% 8.19/2.85  tff(c_90, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_76])).
% 8.19/2.85  tff(c_170, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_90])).
% 8.19/2.85  tff(c_169, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_93])).
% 8.19/2.85  tff(c_327, plain, (![C_84, A_85, B_86]: (v1_partfun1(C_84, A_85) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | v1_xboole_0(B_86))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.19/2.85  tff(c_336, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_169, c_327])).
% 8.19/2.85  tff(c_342, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_170, c_336])).
% 8.19/2.85  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_154, c_342])).
% 8.19/2.85  tff(c_345, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_144])).
% 8.19/2.85  tff(c_350, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_93])).
% 8.19/2.85  tff(c_405, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.19/2.85  tff(c_409, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_350, c_405])).
% 8.19/2.85  tff(c_352, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_85])).
% 8.19/2.85  tff(c_414, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_352])).
% 8.19/2.85  tff(c_351, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_90])).
% 8.19/2.85  tff(c_422, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_351])).
% 8.19/2.85  tff(c_421, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_350])).
% 8.19/2.85  tff(c_2593, plain, (![A_211, B_212, D_213]: (r2_funct_2(A_211, B_212, D_213, D_213) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))) | ~v1_funct_2(D_213, A_211, B_212) | ~v1_funct_1(D_213))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.19/2.85  tff(c_2601, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_2593])).
% 8.19/2.85  tff(c_2609, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_422, c_2601])).
% 8.19/2.85  tff(c_4, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.19/2.85  tff(c_127, plain, (![A_66]: (k4_relat_1(A_66)=k2_funct_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.19/2.85  tff(c_130, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_127])).
% 8.19/2.85  tff(c_133, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_130])).
% 8.19/2.85  tff(c_466, plain, (![A_90, B_91, C_92]: (k3_relset_1(A_90, B_91, C_92)=k4_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.19/2.85  tff(c_469, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_466])).
% 8.19/2.85  tff(c_471, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_469])).
% 8.19/2.85  tff(c_485, plain, (![A_93, B_94, C_95]: (m1_subset_1(k3_relset_1(A_93, B_94, C_95), k1_zfmisc_1(k2_zfmisc_1(B_94, A_93))) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.19/2.85  tff(c_506, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_471, c_485])).
% 8.19/2.85  tff(c_514, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_506])).
% 8.19/2.85  tff(c_2605, plain, (r2_funct_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'), k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_514, c_2593])).
% 8.19/2.85  tff(c_6046, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2605])).
% 8.19/2.85  tff(c_419, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_409])).
% 8.19/2.85  tff(c_6105, plain, (![C_389, A_390, B_391]: (v1_funct_1(k2_funct_1(C_389)) | k2_relset_1(A_390, B_391, C_389)!=B_391 | ~v2_funct_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))) | ~v1_funct_2(C_389, A_390, B_391) | ~v1_funct_1(C_389))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.19/2.85  tff(c_6120, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_6105])).
% 8.19/2.85  tff(c_6131, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_422, c_52, c_419, c_6120])).
% 8.19/2.85  tff(c_6133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6046, c_6131])).
% 8.19/2.85  tff(c_6135, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2605])).
% 8.19/2.85  tff(c_6134, plain, (~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | r2_funct_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'), k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2605])).
% 8.19/2.85  tff(c_6142, plain, (~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6134])).
% 8.19/2.85  tff(c_6252, plain, (![C_398, B_399, A_400]: (v1_funct_2(k2_funct_1(C_398), B_399, A_400) | k2_relset_1(A_400, B_399, C_398)!=B_399 | ~v2_funct_1(C_398) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_400, B_399))) | ~v1_funct_2(C_398, A_400, B_399) | ~v1_funct_1(C_398))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.19/2.85  tff(c_6267, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_6252])).
% 8.19/2.85  tff(c_6278, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_422, c_52, c_419, c_6267])).
% 8.19/2.85  tff(c_6280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6142, c_6278])).
% 8.19/2.85  tff(c_6282, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6134])).
% 8.19/2.85  tff(c_14, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.19/2.85  tff(c_398, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_350, c_14])).
% 8.19/2.85  tff(c_472, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_398])).
% 8.19/2.85  tff(c_539, plain, (![B_96, A_97, C_98]: (k2_relset_1(B_96, A_97, k3_relset_1(A_97, B_96, C_98))=k1_relset_1(A_97, B_96, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.19/2.85  tff(c_545, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_421, c_539])).
% 8.19/2.85  tff(c_549, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_472, c_545])).
% 8.19/2.85  tff(c_6348, plain, (![C_401, A_402, B_403]: (v1_funct_1(k2_funct_1(C_401)) | k2_relset_1(A_402, B_403, C_401)!=B_403 | ~v2_funct_1(C_401) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_2(C_401, A_402, B_403) | ~v1_funct_1(C_401))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.19/2.85  tff(c_6357, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_514, c_6348])).
% 8.19/2.85  tff(c_6372, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6135, c_6282, c_549, c_6357])).
% 8.19/2.85  tff(c_6377, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6372])).
% 8.19/2.85  tff(c_6597, plain, (![A_413, B_414, C_415]: (k2_tops_2(A_413, B_414, C_415)=k2_funct_1(C_415) | ~v2_funct_1(C_415) | k2_relset_1(A_413, B_414, C_415)!=B_414 | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))) | ~v1_funct_2(C_415, A_413, B_414) | ~v1_funct_1(C_415))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.19/2.85  tff(c_6615, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_6597])).
% 8.19/2.85  tff(c_6629, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_422, c_419, c_52, c_6615])).
% 8.19/2.85  tff(c_424, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_74])).
% 8.19/2.85  tff(c_353, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_75])).
% 8.19/2.85  tff(c_7130, plain, (![A_439, B_440, C_441]: (v2_funct_1(k2_tops_2(u1_struct_0(A_439), u1_struct_0(B_440), C_441)) | ~v2_funct_1(C_441) | k2_relset_1(u1_struct_0(A_439), u1_struct_0(B_440), C_441)!=k2_struct_0(B_440) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_439), u1_struct_0(B_440)))) | ~v1_funct_2(C_441, u1_struct_0(A_439), u1_struct_0(B_440)) | ~v1_funct_1(C_441) | ~l1_struct_0(B_440) | ~l1_struct_0(A_439))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.19/2.85  tff(c_7147, plain, (![B_440, C_441]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_440), C_441)) | ~v2_funct_1(C_441) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_440), C_441)!=k2_struct_0(B_440) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_440)))) | ~v1_funct_2(C_441, u1_struct_0('#skF_1'), u1_struct_0(B_440)) | ~v1_funct_1(C_441) | ~l1_struct_0(B_440) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_7130])).
% 8.19/2.85  tff(c_7222, plain, (![B_448, C_449]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0(B_448), C_449)) | ~v2_funct_1(C_449) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0(B_448), C_449)!=k2_struct_0(B_448) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_448)))) | ~v1_funct_2(C_449, k1_relat_1('#skF_3'), u1_struct_0(B_448)) | ~v1_funct_1(C_449) | ~l1_struct_0(B_448))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_353, c_353, c_353, c_7147])).
% 8.19/2.85  tff(c_7233, plain, (![C_449]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_449)) | ~v2_funct_1(C_449) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_449)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_449, k1_relat_1('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_449) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_424, c_7222])).
% 8.19/2.85  tff(c_7358, plain, (![C_456]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_456)) | ~v2_funct_1(C_456) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_456)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_456, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_456))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_424, c_414, c_424, c_424, c_7233])).
% 8.19/2.85  tff(c_7375, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_7358])).
% 8.19/2.85  tff(c_7385, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_422, c_419, c_52, c_6629, c_7375])).
% 8.19/2.85  tff(c_7387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6377, c_7385])).
% 8.19/2.85  tff(c_7389, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6372])).
% 8.19/2.85  tff(c_7530, plain, (![A_460, B_461, C_462]: (k2_tops_2(A_460, B_461, C_462)=k2_funct_1(C_462) | ~v2_funct_1(C_462) | k2_relset_1(A_460, B_461, C_462)!=B_461 | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | ~v1_funct_2(C_462, A_460, B_461) | ~v1_funct_1(C_462))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.19/2.85  tff(c_7533, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_514, c_7530])).
% 8.19/2.85  tff(c_7542, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6135, c_6282, c_549, c_7389, c_7533])).
% 8.19/2.85  tff(c_7539, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_7530])).
% 8.19/2.85  tff(c_7546, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_422, c_419, c_52, c_7539])).
% 8.19/2.85  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.19/2.85  tff(c_108, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_75, c_74, c_74, c_74, c_50])).
% 8.19/2.85  tff(c_348, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_345, c_345, c_108])).
% 8.19/2.85  tff(c_482, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_414, c_414, c_348])).
% 8.19/2.85  tff(c_7547, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7546, c_482])).
% 8.19/2.85  tff(c_7720, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7542, c_7547])).
% 8.19/2.85  tff(c_7727, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_7720])).
% 8.19/2.85  tff(c_7730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_52, c_2609, c_7727])).
% 8.19/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.85  
% 8.19/2.85  Inference rules
% 8.19/2.85  ----------------------
% 8.19/2.85  #Ref     : 0
% 8.19/2.85  #Sup     : 1760
% 8.19/2.85  #Fact    : 0
% 8.19/2.85  #Define  : 0
% 8.19/2.85  #Split   : 54
% 8.19/2.85  #Chain   : 0
% 8.19/2.85  #Close   : 0
% 8.19/2.85  
% 8.19/2.85  Ordering : KBO
% 8.19/2.85  
% 8.19/2.85  Simplification rules
% 8.19/2.85  ----------------------
% 8.19/2.85  #Subsume      : 137
% 8.19/2.85  #Demod        : 2186
% 8.19/2.85  #Tautology    : 742
% 8.19/2.85  #SimpNegUnit  : 48
% 8.19/2.85  #BackRed      : 227
% 8.19/2.85  
% 8.19/2.85  #Partial instantiations: 0
% 8.19/2.85  #Strategies tried      : 1
% 8.19/2.85  
% 8.19/2.85  Timing (in seconds)
% 8.19/2.85  ----------------------
% 8.19/2.85  Preprocessing        : 0.41
% 8.19/2.85  Parsing              : 0.22
% 8.19/2.85  CNF conversion       : 0.02
% 8.19/2.85  Main loop            : 1.65
% 8.19/2.85  Inferencing          : 0.48
% 8.19/2.85  Reduction            : 0.66
% 8.19/2.85  Demodulation         : 0.50
% 8.19/2.85  BG Simplification    : 0.05
% 8.19/2.85  Subsumption          : 0.32
% 8.19/2.85  Abstraction          : 0.08
% 8.19/2.85  MUC search           : 0.00
% 8.19/2.85  Cooper               : 0.00
% 8.19/2.85  Total                : 2.11
% 8.19/2.85  Index Insertion      : 0.00
% 8.19/2.85  Index Deletion       : 0.00
% 8.19/2.85  Index Matching       : 0.00
% 8.19/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
