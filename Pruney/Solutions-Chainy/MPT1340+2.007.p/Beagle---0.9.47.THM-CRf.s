%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:30 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  174 (37683 expanded)
%              Number of leaves         :   45 (13113 expanded)
%              Depth                    :   30
%              Number of atoms          :  474 (109850 expanded)
%              Number of equality atoms :  110 (24750 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_194,negated_conjecture,(
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

tff(f_152,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_160,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_148,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_172,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_69,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_77,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_69])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_76,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_69])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_108,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_58])).

tff(c_156,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_160,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_156])).

tff(c_56,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_87,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_56])).

tff(c_161,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_87])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_93,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(u1_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_93])).

tff(c_103,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99])).

tff(c_104,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_103])).

tff(c_170,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_104])).

tff(c_109,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_109])).

tff(c_115,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_119,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_108,c_115])).

tff(c_127,plain,(
    ! [B_54,A_55] :
      ( k1_relat_1(B_54) = A_55
      | ~ v1_partfun1(B_54,A_55)
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_130,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_119,c_127])).

tff(c_133,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_130])).

tff(c_134,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_78,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_60])).

tff(c_92,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_78])).

tff(c_171,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_92])).

tff(c_169,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_108])).

tff(c_229,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_partfun1(C_63,A_64)
      | ~ v1_funct_2(C_63,A_64,B_65)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | v1_xboole_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_232,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_169,c_229])).

tff(c_235,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_171,c_232])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_134,c_235])).

tff(c_238,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_254,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_108])).

tff(c_314,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_318,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_254,c_314])).

tff(c_257,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_87])).

tff(c_319,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_257])).

tff(c_256,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_92])).

tff(c_326,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_256])).

tff(c_325,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_254])).

tff(c_505,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( r2_funct_2(A_98,B_99,C_100,C_100)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_2(D_101,A_98,B_99)
      | ~ v1_funct_1(D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_2(C_100,A_98,B_99)
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_509,plain,(
    ! [C_100] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_100,C_100)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_100,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_325,c_505])).

tff(c_557,plain,(
    ! [C_105] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_105,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_105,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_509])).

tff(c_562,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_325,c_557])).

tff(c_566,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_562])).

tff(c_324,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_318])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_415,plain,(
    ! [C_82,B_83,A_84] :
      ( v1_funct_2(k2_funct_1(C_82),B_83,A_84)
      | k2_relset_1(A_84,B_83,C_82) != B_83
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83)))
      | ~ v1_funct_2(C_82,A_84,B_83)
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_418,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_325,c_415])).

tff(c_421,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_54,c_324,c_418])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_relat_1(k2_funct_1(A_3)) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_2] :
      ( v2_funct_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_438,plain,(
    ! [C_89,B_90,A_91] :
      ( m1_subset_1(k2_funct_1(C_89),k1_zfmisc_1(k2_zfmisc_1(B_90,A_91)))
      | k2_relset_1(A_91,B_90,C_89) != B_90
      | ~ v2_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90)))
      | ~ v1_funct_2(C_89,A_91,B_90)
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_22,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_471,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(k2_funct_1(C_92))
      | k2_relset_1(A_93,B_94,C_92) != B_94
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_2(C_92,A_93,B_94)
      | ~ v1_funct_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_438,c_22])).

tff(c_477,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_325,c_471])).

tff(c_481,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_54,c_324,c_477])).

tff(c_395,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_funct_1(k2_funct_1(C_76))
      | k2_relset_1(A_77,B_78,C_76) != B_78
      | ~ v2_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(C_76,A_77,B_78)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_398,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_325,c_395])).

tff(c_401,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_54,c_324,c_398])).

tff(c_26,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_482,plain,(
    ! [C_95,B_96,A_97] :
      ( v4_relat_1(k2_funct_1(C_95),B_96)
      | k2_relset_1(A_97,B_96,C_95) != B_96
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_95,A_97,B_96)
      | ~ v1_funct_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_438,c_26])).

tff(c_488,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_325,c_482])).

tff(c_492,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_54,c_324,c_488])).

tff(c_14,plain,(
    ! [A_3] :
      ( k1_relat_1(k2_funct_1(A_3)) = k2_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_240,plain,(
    ! [A_66] :
      ( k1_relat_1(k2_funct_1(A_66)) = k2_relat_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [B_22] :
      ( v1_partfun1(B_22,k1_relat_1(B_22))
      | ~ v4_relat_1(B_22,k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_402,plain,(
    ! [A_79] :
      ( v1_partfun1(k2_funct_1(A_79),k1_relat_1(k2_funct_1(A_79)))
      | ~ v4_relat_1(k2_funct_1(A_79),k2_relat_1(A_79))
      | ~ v1_relat_1(k2_funct_1(A_79))
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_34])).

tff(c_405,plain,(
    ! [A_3] :
      ( v1_partfun1(k2_funct_1(A_3),k2_relat_1(A_3))
      | ~ v4_relat_1(k2_funct_1(A_3),k2_relat_1(A_3))
      | ~ v1_relat_1(k2_funct_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_402])).

tff(c_495,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_492,c_405])).

tff(c_501,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62,c_54,c_481,c_495])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( k1_relat_1(B_22) = A_21
      | ~ v1_partfun1(B_22,A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_498,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_492,c_36])).

tff(c_504,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_498])).

tff(c_515,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_504])).

tff(c_20,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k1_relat_1(A_5)) != k5_relat_1(A_5,B_7)
      | k2_relat_1(A_5) != k1_relat_1(B_7)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_518,plain,(
    ! [B_7] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_7
      | k5_relat_1(k2_funct_1('#skF_3'),B_7) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_7)
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_20])).

tff(c_534,plain,(
    ! [B_7] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_7
      | k5_relat_1(k2_funct_1('#skF_3'),B_7) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_7)
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_401,c_518])).

tff(c_567,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_570,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_567])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62,c_54,c_570])).

tff(c_577,plain,(
    ! [B_106] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_106
      | k5_relat_1(k2_funct_1('#skF_3'),B_106) != k6_relat_1(k2_relat_1('#skF_3'))
      | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(B_106)
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_585,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_577])).

tff(c_591,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62,c_54,c_585])).

tff(c_603,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_606,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_603])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62,c_54,c_606])).

tff(c_612,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_28,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_592,plain,(
    ! [B_107,A_108,C_109] :
      ( k2_relset_1(B_107,A_108,k2_funct_1(C_109)) = k2_relat_1(k2_funct_1(C_109))
      | k2_relset_1(A_108,B_107,C_109) != B_107
      | ~ v2_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ v1_funct_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_438,c_28])).

tff(c_598,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_325,c_592])).

tff(c_602,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_54,c_324,c_598])).

tff(c_677,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_602])).

tff(c_576,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_611,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_406,plain,(
    ! [A_80,B_81] :
      ( k2_funct_1(A_80) = B_81
      | k6_relat_1(k1_relat_1(A_80)) != k5_relat_1(A_80,B_81)
      | k2_relat_1(A_80) != k1_relat_1(B_81)
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_799,plain,(
    ! [A_117] :
      ( k2_funct_1(k2_funct_1(A_117)) = A_117
      | k6_relat_1(k1_relat_1(k2_funct_1(A_117))) != k6_relat_1(k2_relat_1(A_117))
      | k2_relat_1(k2_funct_1(A_117)) != k1_relat_1(A_117)
      | ~ v2_funct_1(k2_funct_1(A_117))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117)
      | ~ v1_funct_1(k2_funct_1(A_117))
      | ~ v1_relat_1(k2_funct_1(A_117))
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_406])).

tff(c_815,plain,(
    ! [A_118] :
      ( k2_funct_1(k2_funct_1(A_118)) = A_118
      | k2_relat_1(k2_funct_1(A_118)) != k1_relat_1(A_118)
      | ~ v2_funct_1(k2_funct_1(A_118))
      | ~ v1_funct_1(k2_funct_1(A_118))
      | ~ v1_relat_1(k2_funct_1(A_118))
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_799])).

tff(c_831,plain,(
    ! [A_119] :
      ( k2_funct_1(k2_funct_1(A_119)) = A_119
      | k2_relat_1(k2_funct_1(A_119)) != k1_relat_1(A_119)
      | ~ v1_funct_1(k2_funct_1(A_119))
      | ~ v1_relat_1(k2_funct_1(A_119))
      | ~ v2_funct_1(A_119)
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_6,c_815])).

tff(c_847,plain,(
    ! [A_120] :
      ( k2_funct_1(k2_funct_1(A_120)) = A_120
      | k2_relat_1(k2_funct_1(A_120)) != k1_relat_1(A_120)
      | ~ v1_funct_1(k2_funct_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_4,c_831])).

tff(c_863,plain,(
    ! [A_121] :
      ( k2_funct_1(k2_funct_1(A_121)) = A_121
      | k2_relat_1(k2_funct_1(A_121)) != k1_relat_1(A_121)
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_2,c_847])).

tff(c_896,plain,(
    ! [A_124] :
      ( k2_funct_1(k2_funct_1(A_124)) = A_124
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_863])).

tff(c_40,plain,(
    ! [C_29,B_28,A_27] :
      ( m1_subset_1(k2_funct_1(C_29),k1_zfmisc_1(k2_zfmisc_1(B_28,A_27)))
      | k2_relset_1(A_27,B_28,C_29) != B_28
      | ~ v2_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1240,plain,(
    ! [A_136,B_137,A_138] :
      ( m1_subset_1(A_136,k1_zfmisc_1(k2_zfmisc_1(B_137,A_138)))
      | k2_relset_1(A_138,B_137,k2_funct_1(A_136)) != B_137
      | ~ v2_funct_1(k2_funct_1(A_136))
      | ~ m1_subset_1(k2_funct_1(A_136),k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_2(k2_funct_1(A_136),A_138,B_137)
      | ~ v1_funct_1(k2_funct_1(A_136))
      | ~ v2_funct_1(A_136)
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_40])).

tff(c_1246,plain,(
    ! [B_137,A_138] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_137,A_138)))
      | k2_relset_1(A_138,B_137,k2_funct_1(k2_funct_1('#skF_3'))) != B_137
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_138,B_137)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_1240])).

tff(c_1264,plain,(
    ! [B_140,A_141] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_140,A_141)))
      | k2_relset_1(A_141,B_140,'#skF_3') != B_140
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2('#skF_3',A_141,B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_401,c_576,c_62,c_611,c_611,c_54,c_611,c_611,c_1246])).

tff(c_50,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_tops_2(A_32,B_33,C_34) = k2_funct_1(C_34)
      | ~ v2_funct_1(C_34)
      | k2_relset_1(A_32,B_33,C_34) != B_33
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1302,plain,(
    ! [B_140,A_141] :
      ( k2_tops_2(B_140,A_141,k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(B_140,A_141,k2_funct_1('#skF_3')) != A_141
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_140,A_141)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | k2_relset_1(A_141,B_140,'#skF_3') != B_140
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2('#skF_3',A_141,B_140) ) ),
    inference(resolution,[status(thm)],[c_1264,c_50])).

tff(c_1430,plain,(
    ! [B_155,A_156] :
      ( k2_tops_2(B_155,A_156,k2_funct_1('#skF_3')) = '#skF_3'
      | k2_relset_1(B_155,A_156,k2_funct_1('#skF_3')) != A_156
      | ~ v1_funct_2(k2_funct_1('#skF_3'),B_155,A_156)
      | k2_relset_1(A_156,B_155,'#skF_3') != B_155
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_156,B_155)))
      | ~ v1_funct_2('#skF_3',A_156,B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_576,c_611,c_1302])).

tff(c_1433,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_325,c_1430])).

tff(c_1436,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_324,c_421,c_677,c_1433])).

tff(c_422,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_tops_2(A_85,B_86,C_87) = k2_funct_1(C_87)
      | ~ v2_funct_1(C_87)
      | k2_relset_1(A_85,B_86,C_87) != B_86
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_425,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_325,c_422])).

tff(c_428,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326,c_324,c_54,c_425])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_114,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_77,c_76,c_76,c_76,c_52])).

tff(c_253,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_238,c_238,c_114])).

tff(c_394,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_319,c_319,c_253])).

tff(c_429,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_394])).

tff(c_1437,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_429])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_1437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.69  
% 4.16/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.70  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.16/1.70  
% 4.16/1.70  %Foreground sorts:
% 4.16/1.70  
% 4.16/1.70  
% 4.16/1.70  %Background operators:
% 4.16/1.70  
% 4.16/1.70  
% 4.16/1.70  %Foreground operators:
% 4.16/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.16/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.16/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.16/1.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.16/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.16/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.70  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.16/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.16/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.16/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.16/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.16/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.16/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.16/1.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.16/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.70  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.16/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.70  
% 4.16/1.72  tff(f_194, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.16/1.72  tff(f_152, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.16/1.72  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.16/1.72  tff(f_160, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.16/1.72  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.16/1.72  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.16/1.72  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.16/1.72  tff(f_110, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.16/1.72  tff(f_132, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.16/1.72  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.16/1.72  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.16/1.72  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.16/1.72  tff(f_45, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.16/1.72  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 4.16/1.72  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.16/1.72  tff(f_172, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.16/1.72  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_69, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.16/1.72  tff(c_77, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_69])).
% 4.16/1.72  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_76, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_69])).
% 4.16/1.72  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_108, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_58])).
% 4.16/1.72  tff(c_156, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.72  tff(c_160, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_156])).
% 4.16/1.72  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_87, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_56])).
% 4.16/1.72  tff(c_161, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_87])).
% 4.16/1.72  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_93, plain, (![A_40]: (~v1_xboole_0(u1_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.16/1.72  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_93])).
% 4.16/1.72  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99])).
% 4.16/1.72  tff(c_104, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_103])).
% 4.16/1.72  tff(c_170, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_104])).
% 4.16/1.72  tff(c_109, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.16/1.72  tff(c_113, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_109])).
% 4.16/1.72  tff(c_115, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.16/1.72  tff(c_119, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_108, c_115])).
% 4.16/1.72  tff(c_127, plain, (![B_54, A_55]: (k1_relat_1(B_54)=A_55 | ~v1_partfun1(B_54, A_55) | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.16/1.72  tff(c_130, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_119, c_127])).
% 4.16/1.72  tff(c_133, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_130])).
% 4.16/1.72  tff(c_134, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_133])).
% 4.16/1.72  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_78, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_60])).
% 4.16/1.72  tff(c_92, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_78])).
% 4.16/1.72  tff(c_171, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_92])).
% 4.16/1.72  tff(c_169, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_108])).
% 4.16/1.72  tff(c_229, plain, (![C_63, A_64, B_65]: (v1_partfun1(C_63, A_64) | ~v1_funct_2(C_63, A_64, B_65) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | v1_xboole_0(B_65))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.16/1.72  tff(c_232, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_169, c_229])).
% 4.16/1.72  tff(c_235, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_171, c_232])).
% 4.16/1.72  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_134, c_235])).
% 4.16/1.72  tff(c_238, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_133])).
% 4.16/1.72  tff(c_254, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_108])).
% 4.16/1.72  tff(c_314, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.72  tff(c_318, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_254, c_314])).
% 4.16/1.72  tff(c_257, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_87])).
% 4.16/1.72  tff(c_319, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_257])).
% 4.16/1.72  tff(c_256, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_92])).
% 4.16/1.72  tff(c_326, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_256])).
% 4.16/1.72  tff(c_325, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_254])).
% 4.16/1.72  tff(c_505, plain, (![A_98, B_99, C_100, D_101]: (r2_funct_2(A_98, B_99, C_100, C_100) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_funct_2(D_101, A_98, B_99) | ~v1_funct_1(D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_funct_2(C_100, A_98, B_99) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.16/1.72  tff(c_509, plain, (![C_100]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_100, C_100) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_100, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_100))), inference(resolution, [status(thm)], [c_325, c_505])).
% 4.16/1.72  tff(c_557, plain, (![C_105]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_105, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_105, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_105))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_509])).
% 4.16/1.72  tff(c_562, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_325, c_557])).
% 4.16/1.72  tff(c_566, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_562])).
% 4.16/1.72  tff(c_324, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_318])).
% 4.16/1.72  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_415, plain, (![C_82, B_83, A_84]: (v1_funct_2(k2_funct_1(C_82), B_83, A_84) | k2_relset_1(A_84, B_83, C_82)!=B_83 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))) | ~v1_funct_2(C_82, A_84, B_83) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.16/1.72  tff(c_418, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_325, c_415])).
% 4.16/1.72  tff(c_421, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_54, c_324, c_418])).
% 4.16/1.72  tff(c_12, plain, (![A_3]: (k2_relat_1(k2_funct_1(A_3))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.16/1.72  tff(c_16, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.16/1.72  tff(c_6, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.16/1.72  tff(c_438, plain, (![C_89, B_90, A_91]: (m1_subset_1(k2_funct_1(C_89), k1_zfmisc_1(k2_zfmisc_1(B_90, A_91))) | k2_relset_1(A_91, B_90, C_89)!=B_90 | ~v2_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))) | ~v1_funct_2(C_89, A_91, B_90) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.16/1.72  tff(c_22, plain, (![C_10, A_8, B_9]: (v1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.16/1.72  tff(c_471, plain, (![C_92, A_93, B_94]: (v1_relat_1(k2_funct_1(C_92)) | k2_relset_1(A_93, B_94, C_92)!=B_94 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_2(C_92, A_93, B_94) | ~v1_funct_1(C_92))), inference(resolution, [status(thm)], [c_438, c_22])).
% 4.16/1.72  tff(c_477, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_325, c_471])).
% 4.16/1.72  tff(c_481, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_54, c_324, c_477])).
% 4.16/1.72  tff(c_395, plain, (![C_76, A_77, B_78]: (v1_funct_1(k2_funct_1(C_76)) | k2_relset_1(A_77, B_78, C_76)!=B_78 | ~v2_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(C_76, A_77, B_78) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.16/1.72  tff(c_398, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_325, c_395])).
% 4.16/1.72  tff(c_401, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_54, c_324, c_398])).
% 4.16/1.72  tff(c_26, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.16/1.72  tff(c_482, plain, (![C_95, B_96, A_97]: (v4_relat_1(k2_funct_1(C_95), B_96) | k2_relset_1(A_97, B_96, C_95)!=B_96 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_95, A_97, B_96) | ~v1_funct_1(C_95))), inference(resolution, [status(thm)], [c_438, c_26])).
% 4.16/1.72  tff(c_488, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_325, c_482])).
% 4.16/1.72  tff(c_492, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_54, c_324, c_488])).
% 4.16/1.72  tff(c_14, plain, (![A_3]: (k1_relat_1(k2_funct_1(A_3))=k2_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.16/1.72  tff(c_240, plain, (![A_66]: (k1_relat_1(k2_funct_1(A_66))=k2_relat_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.16/1.72  tff(c_34, plain, (![B_22]: (v1_partfun1(B_22, k1_relat_1(B_22)) | ~v4_relat_1(B_22, k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.16/1.72  tff(c_402, plain, (![A_79]: (v1_partfun1(k2_funct_1(A_79), k1_relat_1(k2_funct_1(A_79))) | ~v4_relat_1(k2_funct_1(A_79), k2_relat_1(A_79)) | ~v1_relat_1(k2_funct_1(A_79)) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_240, c_34])).
% 4.16/1.72  tff(c_405, plain, (![A_3]: (v1_partfun1(k2_funct_1(A_3), k2_relat_1(A_3)) | ~v4_relat_1(k2_funct_1(A_3), k2_relat_1(A_3)) | ~v1_relat_1(k2_funct_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_14, c_402])).
% 4.16/1.72  tff(c_495, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_492, c_405])).
% 4.16/1.72  tff(c_501, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_62, c_54, c_481, c_495])).
% 4.16/1.72  tff(c_36, plain, (![B_22, A_21]: (k1_relat_1(B_22)=A_21 | ~v1_partfun1(B_22, A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.16/1.72  tff(c_498, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_492, c_36])).
% 4.16/1.72  tff(c_504, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_498])).
% 4.16/1.72  tff(c_515, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_501, c_504])).
% 4.16/1.72  tff(c_20, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k1_relat_1(A_5))!=k5_relat_1(A_5, B_7) | k2_relat_1(A_5)!=k1_relat_1(B_7) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.16/1.72  tff(c_518, plain, (![B_7]: (k2_funct_1(k2_funct_1('#skF_3'))=B_7 | k5_relat_1(k2_funct_1('#skF_3'), B_7)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_7) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_515, c_20])).
% 4.16/1.72  tff(c_534, plain, (![B_7]: (k2_funct_1(k2_funct_1('#skF_3'))=B_7 | k5_relat_1(k2_funct_1('#skF_3'), B_7)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_7) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_401, c_518])).
% 4.16/1.72  tff(c_567, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_534])).
% 4.16/1.72  tff(c_570, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_567])).
% 4.16/1.72  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_62, c_54, c_570])).
% 4.16/1.72  tff(c_577, plain, (![B_106]: (k2_funct_1(k2_funct_1('#skF_3'))=B_106 | k5_relat_1(k2_funct_1('#skF_3'), B_106)!=k6_relat_1(k2_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(B_106) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(splitRight, [status(thm)], [c_534])).
% 4.16/1.72  tff(c_585, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_577])).
% 4.16/1.72  tff(c_591, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_62, c_54, c_585])).
% 4.16/1.72  tff(c_603, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_591])).
% 4.16/1.72  tff(c_606, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_603])).
% 4.16/1.72  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_62, c_54, c_606])).
% 4.16/1.72  tff(c_612, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_591])).
% 4.16/1.72  tff(c_28, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.72  tff(c_592, plain, (![B_107, A_108, C_109]: (k2_relset_1(B_107, A_108, k2_funct_1(C_109))=k2_relat_1(k2_funct_1(C_109)) | k2_relset_1(A_108, B_107, C_109)!=B_107 | ~v2_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_109, A_108, B_107) | ~v1_funct_1(C_109))), inference(resolution, [status(thm)], [c_438, c_28])).
% 4.16/1.72  tff(c_598, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_325, c_592])).
% 4.16/1.72  tff(c_602, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_54, c_324, c_598])).
% 4.16/1.72  tff(c_677, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_602])).
% 4.16/1.72  tff(c_576, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_534])).
% 4.16/1.72  tff(c_611, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_591])).
% 4.16/1.72  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.72  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.72  tff(c_406, plain, (![A_80, B_81]: (k2_funct_1(A_80)=B_81 | k6_relat_1(k1_relat_1(A_80))!=k5_relat_1(A_80, B_81) | k2_relat_1(A_80)!=k1_relat_1(B_81) | ~v2_funct_1(A_80) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.16/1.72  tff(c_799, plain, (![A_117]: (k2_funct_1(k2_funct_1(A_117))=A_117 | k6_relat_1(k1_relat_1(k2_funct_1(A_117)))!=k6_relat_1(k2_relat_1(A_117)) | k2_relat_1(k2_funct_1(A_117))!=k1_relat_1(A_117) | ~v2_funct_1(k2_funct_1(A_117)) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117) | ~v1_funct_1(k2_funct_1(A_117)) | ~v1_relat_1(k2_funct_1(A_117)) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_16, c_406])).
% 4.16/1.72  tff(c_815, plain, (![A_118]: (k2_funct_1(k2_funct_1(A_118))=A_118 | k2_relat_1(k2_funct_1(A_118))!=k1_relat_1(A_118) | ~v2_funct_1(k2_funct_1(A_118)) | ~v1_funct_1(k2_funct_1(A_118)) | ~v1_relat_1(k2_funct_1(A_118)) | ~v2_funct_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_14, c_799])).
% 4.16/1.72  tff(c_831, plain, (![A_119]: (k2_funct_1(k2_funct_1(A_119))=A_119 | k2_relat_1(k2_funct_1(A_119))!=k1_relat_1(A_119) | ~v1_funct_1(k2_funct_1(A_119)) | ~v1_relat_1(k2_funct_1(A_119)) | ~v2_funct_1(A_119) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_6, c_815])).
% 4.16/1.72  tff(c_847, plain, (![A_120]: (k2_funct_1(k2_funct_1(A_120))=A_120 | k2_relat_1(k2_funct_1(A_120))!=k1_relat_1(A_120) | ~v1_funct_1(k2_funct_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_4, c_831])).
% 4.16/1.72  tff(c_863, plain, (![A_121]: (k2_funct_1(k2_funct_1(A_121))=A_121 | k2_relat_1(k2_funct_1(A_121))!=k1_relat_1(A_121) | ~v2_funct_1(A_121) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_2, c_847])).
% 4.16/1.72  tff(c_896, plain, (![A_124]: (k2_funct_1(k2_funct_1(A_124))=A_124 | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_12, c_863])).
% 4.16/1.72  tff(c_40, plain, (![C_29, B_28, A_27]: (m1_subset_1(k2_funct_1(C_29), k1_zfmisc_1(k2_zfmisc_1(B_28, A_27))) | k2_relset_1(A_27, B_28, C_29)!=B_28 | ~v2_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.16/1.72  tff(c_1240, plain, (![A_136, B_137, A_138]: (m1_subset_1(A_136, k1_zfmisc_1(k2_zfmisc_1(B_137, A_138))) | k2_relset_1(A_138, B_137, k2_funct_1(A_136))!=B_137 | ~v2_funct_1(k2_funct_1(A_136)) | ~m1_subset_1(k2_funct_1(A_136), k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_2(k2_funct_1(A_136), A_138, B_137) | ~v1_funct_1(k2_funct_1(A_136)) | ~v2_funct_1(A_136) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_896, c_40])).
% 4.16/1.72  tff(c_1246, plain, (![B_137, A_138]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_137, A_138))) | k2_relset_1(A_138, B_137, k2_funct_1(k2_funct_1('#skF_3')))!=B_137 | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_138, B_137) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_611, c_1240])).
% 4.16/1.72  tff(c_1264, plain, (![B_140, A_141]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_140, A_141))) | k2_relset_1(A_141, B_140, '#skF_3')!=B_140 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2('#skF_3', A_141, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_401, c_576, c_62, c_611, c_611, c_54, c_611, c_611, c_1246])).
% 4.16/1.72  tff(c_50, plain, (![A_32, B_33, C_34]: (k2_tops_2(A_32, B_33, C_34)=k2_funct_1(C_34) | ~v2_funct_1(C_34) | k2_relset_1(A_32, B_33, C_34)!=B_33 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.16/1.72  tff(c_1302, plain, (![B_140, A_141]: (k2_tops_2(B_140, A_141, k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(B_140, A_141, k2_funct_1('#skF_3'))!=A_141 | ~v1_funct_2(k2_funct_1('#skF_3'), B_140, A_141) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(A_141, B_140, '#skF_3')!=B_140 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2('#skF_3', A_141, B_140))), inference(resolution, [status(thm)], [c_1264, c_50])).
% 4.16/1.72  tff(c_1430, plain, (![B_155, A_156]: (k2_tops_2(B_155, A_156, k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(B_155, A_156, k2_funct_1('#skF_3'))!=A_156 | ~v1_funct_2(k2_funct_1('#skF_3'), B_155, A_156) | k2_relset_1(A_156, B_155, '#skF_3')!=B_155 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))) | ~v1_funct_2('#skF_3', A_156, B_155))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_576, c_611, c_1302])).
% 4.16/1.72  tff(c_1433, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3' | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_325, c_1430])).
% 4.16/1.72  tff(c_1436, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_324, c_421, c_677, c_1433])).
% 4.16/1.72  tff(c_422, plain, (![A_85, B_86, C_87]: (k2_tops_2(A_85, B_86, C_87)=k2_funct_1(C_87) | ~v2_funct_1(C_87) | k2_relset_1(A_85, B_86, C_87)!=B_86 | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_87, A_85, B_86) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.16/1.72  tff(c_425, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_325, c_422])).
% 4.16/1.72  tff(c_428, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326, c_324, c_54, c_425])).
% 4.16/1.72  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.16/1.72  tff(c_114, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_77, c_76, c_76, c_76, c_52])).
% 4.16/1.72  tff(c_253, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_238, c_238, c_114])).
% 4.16/1.72  tff(c_394, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_319, c_319, c_253])).
% 4.16/1.72  tff(c_429, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_394])).
% 4.16/1.72  tff(c_1437, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_429])).
% 4.16/1.72  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_566, c_1437])).
% 4.16/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.72  
% 4.16/1.72  Inference rules
% 4.16/1.72  ----------------------
% 4.16/1.72  #Ref     : 0
% 4.16/1.72  #Sup     : 298
% 4.16/1.72  #Fact    : 0
% 4.16/1.72  #Define  : 0
% 4.16/1.72  #Split   : 4
% 4.16/1.72  #Chain   : 0
% 4.16/1.72  #Close   : 0
% 4.16/1.72  
% 4.16/1.72  Ordering : KBO
% 4.16/1.72  
% 4.16/1.72  Simplification rules
% 4.16/1.72  ----------------------
% 4.16/1.72  #Subsume      : 27
% 4.16/1.72  #Demod        : 765
% 4.16/1.72  #Tautology    : 181
% 4.16/1.72  #SimpNegUnit  : 8
% 4.16/1.72  #BackRed      : 27
% 4.16/1.72  
% 4.16/1.72  #Partial instantiations: 0
% 4.16/1.72  #Strategies tried      : 1
% 4.16/1.72  
% 4.16/1.72  Timing (in seconds)
% 4.16/1.72  ----------------------
% 4.16/1.73  Preprocessing        : 0.37
% 4.16/1.73  Parsing              : 0.20
% 4.16/1.73  CNF conversion       : 0.02
% 4.16/1.73  Main loop            : 0.55
% 4.16/1.73  Inferencing          : 0.19
% 4.16/1.73  Reduction            : 0.19
% 4.16/1.73  Demodulation         : 0.14
% 4.16/1.73  BG Simplification    : 0.03
% 4.16/1.73  Subsumption          : 0.10
% 4.16/1.73  Abstraction          : 0.03
% 4.16/1.73  MUC search           : 0.00
% 4.16/1.73  Cooper               : 0.00
% 4.16/1.73  Total                : 0.99
% 4.16/1.73  Index Insertion      : 0.00
% 4.16/1.73  Index Deletion       : 0.00
% 4.16/1.73  Index Matching       : 0.00
% 4.16/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
