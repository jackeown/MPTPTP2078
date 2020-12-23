%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:42 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  133 (6851 expanded)
%              Number of leaves         :   42 (2438 expanded)
%              Depth                    :   19
%              Number of atoms          :  326 (19995 expanded)
%              Number of equality atoms :   70 (4618 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_180,negated_conjecture,(
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

tff(f_120,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_100,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_116,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_158,axiom,(
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

tff(c_60,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_70,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_62])).

tff(c_56,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_69,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_62])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_81,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_50])).

tff(c_82,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_81,c_82])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_85])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_157,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_157])).

tff(c_48,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_89,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_48])).

tff(c_162,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_89])).

tff(c_38,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(k2_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_176,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_38])).

tff(c_180,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_176])).

tff(c_181,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_180])).

tff(c_99,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_81,c_99])).

tff(c_150,plain,(
    ! [B_59,A_60] :
      ( k1_relat_1(B_59) = A_60
      | ~ v1_partfun1(B_59,A_60)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_153,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_150])).

tff(c_156,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_153])).

tff(c_211,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_79,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_52])).

tff(c_171,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_79])).

tff(c_170,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_81])).

tff(c_219,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_partfun1(C_67,A_68)
      | ~ v1_funct_2(C_67,A_68,B_69)
      | ~ v1_funct_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | v1_xboole_0(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_222,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_170,c_219])).

tff(c_225,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_171,c_222])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_211,c_225])).

tff(c_228,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_232,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_171])).

tff(c_231,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_170])).

tff(c_26,plain,(
    ! [A_20,B_21,D_23] :
      ( r2_funct_2(A_20,B_21,D_23,D_23)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_23,A_20,B_21)
      | ~ v1_funct_1(D_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_271,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_26])).

tff(c_286,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_271])).

tff(c_10,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_199,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_16])).

tff(c_265,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_199])).

tff(c_305,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_funct_1(k2_funct_1(C_76))
      | k2_relset_1(A_77,B_78,C_76) != B_78
      | ~ v2_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(C_76,A_77,B_78)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_308,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_305])).

tff(c_311,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_46,c_265,c_308])).

tff(c_322,plain,(
    ! [C_80,B_81,A_82] :
      ( v1_funct_2(k2_funct_1(C_80),B_81,A_82)
      | k2_relset_1(A_82,B_81,C_80) != B_81
      | ~ v2_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81)))
      | ~ v1_funct_2(C_80,A_82,B_81)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_325,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_322])).

tff(c_328,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_46,c_265,c_325])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_329,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_tops_2(A_83,B_84,C_85) = k2_funct_1(C_85)
      | ~ v2_funct_1(C_85)
      | k2_relset_1(A_83,B_84,C_85) != B_84
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_332,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_329])).

tff(c_335,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_265,c_46,c_332])).

tff(c_234,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_70])).

tff(c_172,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_69])).

tff(c_510,plain,(
    ! [A_108,B_109,C_110] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_108),u1_struct_0(B_109),C_110))
      | ~ v2_funct_1(C_110)
      | k2_relset_1(u1_struct_0(A_108),u1_struct_0(B_109),C_110) != k2_struct_0(B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ l1_struct_0(B_109)
      | ~ l1_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_526,plain,(
    ! [A_108,C_110] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_108),u1_struct_0('#skF_2'),C_110))
      | ~ v2_funct_1(C_110)
      | k2_relset_1(u1_struct_0(A_108),u1_struct_0('#skF_2'),C_110) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_110)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_510])).

tff(c_595,plain,(
    ! [A_124,C_125] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_124),k2_relat_1('#skF_3'),C_125))
      | ~ v2_funct_1(C_125)
      | k2_relset_1(u1_struct_0(A_124),k2_relat_1('#skF_3'),C_125) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_124),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_125,u1_struct_0(A_124),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_125)
      | ~ l1_struct_0(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_172,c_162,c_172,c_172,c_526])).

tff(c_602,plain,(
    ! [C_125] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_125))
      | ~ v2_funct_1(C_125)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_125) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_125,u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_125)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_595])).

tff(c_611,plain,(
    ! [C_126] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_126))
      | ~ v2_funct_1(C_126)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_126) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_126,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_234,c_234,c_234,c_602])).

tff(c_618,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_611])).

tff(c_622,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_265,c_46,c_335,c_618])).

tff(c_348,plain,(
    ! [C_87,B_88,A_89] :
      ( m1_subset_1(k2_funct_1(C_87),k1_zfmisc_1(k2_zfmisc_1(B_88,A_89)))
      | k2_relset_1(A_89,B_88,C_87) != B_88
      | ~ v2_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88)))
      | ~ v1_funct_2(C_87,A_89,B_88)
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_462,plain,(
    ! [B_99,A_100,C_101] :
      ( k2_relset_1(B_99,A_100,k2_funct_1(C_101)) = k2_relat_1(k2_funct_1(C_101))
      | k2_relset_1(A_100,B_99,C_101) != B_99
      | ~ v2_funct_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99)))
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ v1_funct_1(C_101) ) ),
    inference(resolution,[status(thm)],[c_348,c_16])).

tff(c_468,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_462])).

tff(c_472,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_46,c_265,c_468])).

tff(c_34,plain,(
    ! [C_26,A_24,B_25] :
      ( v1_funct_1(k2_funct_1(C_26))
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_794,plain,(
    ! [C_138,B_139,A_140] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_138)))
      | k2_relset_1(B_139,A_140,k2_funct_1(C_138)) != A_140
      | ~ v2_funct_1(k2_funct_1(C_138))
      | ~ v1_funct_2(k2_funct_1(C_138),B_139,A_140)
      | ~ v1_funct_1(k2_funct_1(C_138))
      | k2_relset_1(A_140,B_139,C_138) != B_139
      | ~ v2_funct_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139)))
      | ~ v1_funct_2(C_138,A_140,B_139)
      | ~ v1_funct_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_348,c_34])).

tff(c_800,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_794])).

tff(c_804,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_46,c_265,c_311,c_328,c_622,c_472,c_800])).

tff(c_806,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_804])).

tff(c_809,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_806])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_54,c_46,c_809])).

tff(c_815,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_804])).

tff(c_827,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_472])).

tff(c_40,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_tops_2(A_29,B_30,C_31) = k2_funct_1(C_31)
      | ~ v2_funct_1(C_31)
      | k2_relset_1(A_29,B_30,C_31) != B_30
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_975,plain,(
    ! [B_146,A_147,C_148] :
      ( k2_tops_2(B_146,A_147,k2_funct_1(C_148)) = k2_funct_1(k2_funct_1(C_148))
      | ~ v2_funct_1(k2_funct_1(C_148))
      | k2_relset_1(B_146,A_147,k2_funct_1(C_148)) != A_147
      | ~ v1_funct_2(k2_funct_1(C_148),B_146,A_147)
      | ~ v1_funct_1(k2_funct_1(C_148))
      | k2_relset_1(A_147,B_146,C_148) != B_146
      | ~ v2_funct_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ v1_funct_1(C_148) ) ),
    inference(resolution,[status(thm)],[c_348,c_40])).

tff(c_981,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_975])).

tff(c_985,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232,c_46,c_265,c_311,c_328,c_827,c_622,c_981])).

tff(c_44,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_104,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_70,c_69,c_69,c_69,c_44])).

tff(c_168,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_162,c_162,c_104])).

tff(c_264,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_228,c_168])).

tff(c_336,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_264])).

tff(c_986,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_336])).

tff(c_993,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_986])).

tff(c_996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_54,c_46,c_286,c_993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  
% 3.53/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.53/1.59  
% 3.53/1.59  %Foreground sorts:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Background operators:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Foreground operators:
% 3.53/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.53/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.53/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.53/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.59  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.53/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.53/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.53/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.59  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.53/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.59  
% 3.82/1.61  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.82/1.61  tff(f_180, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.82/1.61  tff(f_120, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.82/1.61  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.82/1.61  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.82/1.61  tff(f_128, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.82/1.61  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.82/1.61  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.82/1.61  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.82/1.61  tff(f_100, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.82/1.61  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.82/1.61  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.82/1.61  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.82/1.61  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.82/1.61  tff(f_158, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 3.82/1.61  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.82/1.61  tff(c_60, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_62, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.82/1.61  tff(c_70, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_62])).
% 3.82/1.61  tff(c_56, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_69, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_62])).
% 3.82/1.61  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_81, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_50])).
% 3.82/1.61  tff(c_82, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.82/1.61  tff(c_85, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_81, c_82])).
% 3.82/1.61  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_85])).
% 3.82/1.61  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_157, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.82/1.61  tff(c_161, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_81, c_157])).
% 3.82/1.61  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_89, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_48])).
% 3.82/1.61  tff(c_162, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_89])).
% 3.82/1.61  tff(c_38, plain, (![A_28]: (~v1_xboole_0(k2_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.82/1.61  tff(c_176, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_162, c_38])).
% 3.82/1.61  tff(c_180, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_176])).
% 3.82/1.61  tff(c_181, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_180])).
% 3.82/1.61  tff(c_99, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.61  tff(c_103, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_81, c_99])).
% 3.82/1.61  tff(c_150, plain, (![B_59, A_60]: (k1_relat_1(B_59)=A_60 | ~v1_partfun1(B_59, A_60) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.82/1.61  tff(c_153, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_150])).
% 3.82/1.61  tff(c_156, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_153])).
% 3.82/1.61  tff(c_211, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_156])).
% 3.82/1.61  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_79, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_52])).
% 3.82/1.61  tff(c_171, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_79])).
% 3.82/1.61  tff(c_170, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_81])).
% 3.82/1.61  tff(c_219, plain, (![C_67, A_68, B_69]: (v1_partfun1(C_67, A_68) | ~v1_funct_2(C_67, A_68, B_69) | ~v1_funct_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | v1_xboole_0(B_69))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.82/1.61  tff(c_222, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_170, c_219])).
% 3.82/1.61  tff(c_225, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_171, c_222])).
% 3.82/1.61  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_211, c_225])).
% 3.82/1.61  tff(c_228, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_156])).
% 3.82/1.61  tff(c_232, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_171])).
% 3.82/1.61  tff(c_231, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_170])).
% 3.82/1.61  tff(c_26, plain, (![A_20, B_21, D_23]: (r2_funct_2(A_20, B_21, D_23, D_23) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(D_23, A_20, B_21) | ~v1_funct_1(D_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.82/1.61  tff(c_271, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_26])).
% 3.82/1.61  tff(c_286, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_271])).
% 3.82/1.61  tff(c_10, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.61  tff(c_16, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.82/1.61  tff(c_199, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_170, c_16])).
% 3.82/1.61  tff(c_265, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_199])).
% 3.82/1.61  tff(c_305, plain, (![C_76, A_77, B_78]: (v1_funct_1(k2_funct_1(C_76)) | k2_relset_1(A_77, B_78, C_76)!=B_78 | ~v2_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(C_76, A_77, B_78) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.82/1.61  tff(c_308, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_305])).
% 3.82/1.61  tff(c_311, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_46, c_265, c_308])).
% 3.82/1.61  tff(c_322, plain, (![C_80, B_81, A_82]: (v1_funct_2(k2_funct_1(C_80), B_81, A_82) | k2_relset_1(A_82, B_81, C_80)!=B_81 | ~v2_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))) | ~v1_funct_2(C_80, A_82, B_81) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.82/1.61  tff(c_325, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_322])).
% 3.82/1.61  tff(c_328, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_46, c_265, c_325])).
% 3.82/1.61  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.82/1.61  tff(c_329, plain, (![A_83, B_84, C_85]: (k2_tops_2(A_83, B_84, C_85)=k2_funct_1(C_85) | ~v2_funct_1(C_85) | k2_relset_1(A_83, B_84, C_85)!=B_84 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.82/1.61  tff(c_332, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_329])).
% 3.82/1.61  tff(c_335, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_265, c_46, c_332])).
% 3.82/1.61  tff(c_234, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_70])).
% 3.82/1.61  tff(c_172, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_69])).
% 3.82/1.61  tff(c_510, plain, (![A_108, B_109, C_110]: (v2_funct_1(k2_tops_2(u1_struct_0(A_108), u1_struct_0(B_109), C_110)) | ~v2_funct_1(C_110) | k2_relset_1(u1_struct_0(A_108), u1_struct_0(B_109), C_110)!=k2_struct_0(B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), u1_struct_0(B_109)))) | ~v1_funct_2(C_110, u1_struct_0(A_108), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~l1_struct_0(B_109) | ~l1_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.82/1.61  tff(c_526, plain, (![A_108, C_110]: (v2_funct_1(k2_tops_2(u1_struct_0(A_108), u1_struct_0('#skF_2'), C_110)) | ~v2_funct_1(C_110) | k2_relset_1(u1_struct_0(A_108), u1_struct_0('#skF_2'), C_110)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_110, u1_struct_0(A_108), u1_struct_0('#skF_2')) | ~v1_funct_1(C_110) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_108))), inference(superposition, [status(thm), theory('equality')], [c_172, c_510])).
% 3.82/1.61  tff(c_595, plain, (![A_124, C_125]: (v2_funct_1(k2_tops_2(u1_struct_0(A_124), k2_relat_1('#skF_3'), C_125)) | ~v2_funct_1(C_125) | k2_relset_1(u1_struct_0(A_124), k2_relat_1('#skF_3'), C_125)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_124), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_125, u1_struct_0(A_124), k2_relat_1('#skF_3')) | ~v1_funct_1(C_125) | ~l1_struct_0(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_172, c_162, c_172, c_172, c_526])).
% 3.82/1.61  tff(c_602, plain, (![C_125]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_125)) | ~v2_funct_1(C_125) | k2_relset_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_125)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_125, u1_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_125) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_595])).
% 3.82/1.61  tff(c_611, plain, (![C_126]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_126)) | ~v2_funct_1(C_126) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_126)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_126, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_126))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_234, c_234, c_234, c_602])).
% 3.82/1.61  tff(c_618, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_611])).
% 3.82/1.61  tff(c_622, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_265, c_46, c_335, c_618])).
% 3.82/1.61  tff(c_348, plain, (![C_87, B_88, A_89]: (m1_subset_1(k2_funct_1(C_87), k1_zfmisc_1(k2_zfmisc_1(B_88, A_89))) | k2_relset_1(A_89, B_88, C_87)!=B_88 | ~v2_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))) | ~v1_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.82/1.61  tff(c_462, plain, (![B_99, A_100, C_101]: (k2_relset_1(B_99, A_100, k2_funct_1(C_101))=k2_relat_1(k2_funct_1(C_101)) | k2_relset_1(A_100, B_99, C_101)!=B_99 | ~v2_funct_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))) | ~v1_funct_2(C_101, A_100, B_99) | ~v1_funct_1(C_101))), inference(resolution, [status(thm)], [c_348, c_16])).
% 3.82/1.61  tff(c_468, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_462])).
% 3.82/1.61  tff(c_472, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_46, c_265, c_468])).
% 3.82/1.61  tff(c_34, plain, (![C_26, A_24, B_25]: (v1_funct_1(k2_funct_1(C_26)) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.82/1.61  tff(c_794, plain, (![C_138, B_139, A_140]: (v1_funct_1(k2_funct_1(k2_funct_1(C_138))) | k2_relset_1(B_139, A_140, k2_funct_1(C_138))!=A_140 | ~v2_funct_1(k2_funct_1(C_138)) | ~v1_funct_2(k2_funct_1(C_138), B_139, A_140) | ~v1_funct_1(k2_funct_1(C_138)) | k2_relset_1(A_140, B_139, C_138)!=B_139 | ~v2_funct_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))) | ~v1_funct_2(C_138, A_140, B_139) | ~v1_funct_1(C_138))), inference(resolution, [status(thm)], [c_348, c_34])).
% 3.82/1.61  tff(c_800, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_794])).
% 3.82/1.61  tff(c_804, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_46, c_265, c_311, c_328, c_622, c_472, c_800])).
% 3.82/1.61  tff(c_806, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_804])).
% 3.82/1.61  tff(c_809, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_806])).
% 3.82/1.61  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_54, c_46, c_809])).
% 3.82/1.61  tff(c_815, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_804])).
% 3.82/1.61  tff(c_827, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_815, c_472])).
% 3.82/1.61  tff(c_40, plain, (![A_29, B_30, C_31]: (k2_tops_2(A_29, B_30, C_31)=k2_funct_1(C_31) | ~v2_funct_1(C_31) | k2_relset_1(A_29, B_30, C_31)!=B_30 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.82/1.61  tff(c_975, plain, (![B_146, A_147, C_148]: (k2_tops_2(B_146, A_147, k2_funct_1(C_148))=k2_funct_1(k2_funct_1(C_148)) | ~v2_funct_1(k2_funct_1(C_148)) | k2_relset_1(B_146, A_147, k2_funct_1(C_148))!=A_147 | ~v1_funct_2(k2_funct_1(C_148), B_146, A_147) | ~v1_funct_1(k2_funct_1(C_148)) | k2_relset_1(A_147, B_146, C_148)!=B_146 | ~v2_funct_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))) | ~v1_funct_2(C_148, A_147, B_146) | ~v1_funct_1(C_148))), inference(resolution, [status(thm)], [c_348, c_40])).
% 3.82/1.61  tff(c_981, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_975])).
% 3.82/1.61  tff(c_985, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232, c_46, c_265, c_311, c_328, c_827, c_622, c_981])).
% 3.82/1.61  tff(c_44, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.82/1.61  tff(c_104, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_70, c_69, c_69, c_69, c_44])).
% 3.82/1.61  tff(c_168, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_162, c_162, c_104])).
% 3.82/1.61  tff(c_264, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_228, c_168])).
% 3.82/1.61  tff(c_336, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_264])).
% 3.82/1.61  tff(c_986, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_985, c_336])).
% 3.82/1.61  tff(c_993, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_986])).
% 3.82/1.61  tff(c_996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_54, c_46, c_286, c_993])).
% 3.82/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.61  
% 3.82/1.61  Inference rules
% 3.82/1.61  ----------------------
% 3.82/1.61  #Ref     : 0
% 3.82/1.61  #Sup     : 196
% 3.82/1.61  #Fact    : 0
% 3.82/1.61  #Define  : 0
% 3.82/1.61  #Split   : 8
% 3.82/1.61  #Chain   : 0
% 3.82/1.61  #Close   : 0
% 3.82/1.61  
% 3.82/1.61  Ordering : KBO
% 3.82/1.61  
% 3.82/1.61  Simplification rules
% 3.82/1.61  ----------------------
% 3.82/1.61  #Subsume      : 6
% 3.82/1.61  #Demod        : 383
% 3.82/1.61  #Tautology    : 91
% 3.82/1.61  #SimpNegUnit  : 4
% 3.82/1.61  #BackRed      : 17
% 3.82/1.61  
% 3.82/1.61  #Partial instantiations: 0
% 3.82/1.61  #Strategies tried      : 1
% 3.82/1.61  
% 3.82/1.61  Timing (in seconds)
% 3.82/1.61  ----------------------
% 3.82/1.62  Preprocessing        : 0.34
% 3.82/1.62  Parsing              : 0.18
% 3.82/1.62  CNF conversion       : 0.02
% 3.82/1.62  Main loop            : 0.46
% 3.82/1.62  Inferencing          : 0.16
% 3.82/1.62  Reduction            : 0.16
% 3.82/1.62  Demodulation         : 0.12
% 3.82/1.62  BG Simplification    : 0.03
% 3.82/1.62  Subsumption          : 0.08
% 3.82/1.62  Abstraction          : 0.02
% 3.82/1.62  MUC search           : 0.00
% 3.82/1.62  Cooper               : 0.00
% 3.82/1.62  Total                : 0.85
% 3.82/1.62  Index Insertion      : 0.00
% 3.82/1.62  Index Deletion       : 0.00
% 3.82/1.62  Index Matching       : 0.00
% 3.82/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
