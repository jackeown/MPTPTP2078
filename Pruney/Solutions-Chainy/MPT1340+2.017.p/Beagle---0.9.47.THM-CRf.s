%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:31 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  182 (27719 expanded)
%              Number of leaves         :   50 (9653 expanded)
%              Depth                    :   23
%              Number of atoms          :  434 (80386 expanded)
%              Number of equality atoms :  110 (18214 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(f_225,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_183,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_191,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_169,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_153,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_55,axiom,(
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

tff(f_179,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_203,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_80,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_95,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_103,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_95])).

tff(c_76,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_102,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_95])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_135,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_102,c_70])).

tff(c_22,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_139,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_22])).

tff(c_145,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_149,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_135,c_145])).

tff(c_180,plain,(
    ! [B_65,A_66] :
      ( k1_relat_1(B_65) = A_66
      | ~ v1_partfun1(B_65,A_66)
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_183,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_180])).

tff(c_186,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_183])).

tff(c_187,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_224,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_232,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_224])).

tff(c_68,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_128,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_102,c_68])).

tff(c_237,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_128])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_104,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_72])).

tff(c_113,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_104])).

tff(c_247,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_113])).

tff(c_245,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_135])).

tff(c_303,plain,(
    ! [B_77,C_78,A_79] :
      ( k1_xboole_0 = B_77
      | v1_partfun1(C_78,A_79)
      | ~ v1_funct_2(C_78,A_79,B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_77)))
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_306,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_245,c_303])).

tff(c_312,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_247,c_306])).

tff(c_313,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_312])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_115,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(u1_struct_0(A_50))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_121,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_115])).

tff(c_125,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_121])).

tff(c_126,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_125])).

tff(c_246,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_126])).

tff(c_320,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_246])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_325,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_329,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_135])).

tff(c_420,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_427,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_329,c_420])).

tff(c_330,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_128])).

tff(c_429,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_330])).

tff(c_332,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_113])).

tff(c_435,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_332])).

tff(c_436,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_329])).

tff(c_1194,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( r2_funct_2(A_136,B_137,C_138,C_138)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_2(D_139,A_136,B_137)
      | ~ v1_funct_1(D_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_2(C_138,A_136,B_137)
      | ~ v1_funct_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1204,plain,(
    ! [C_138] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_138,C_138)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_138,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_436,c_1194])).

tff(c_1245,plain,(
    ! [C_140] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_140,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_140,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_1204])).

tff(c_1250,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_1245])).

tff(c_1257,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_1250])).

tff(c_434,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_427])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_969,plain,(
    ! [B_130,C_131,A_132] :
      ( k6_partfun1(B_130) = k5_relat_1(k2_funct_1(C_131),C_131)
      | k1_xboole_0 = B_130
      | ~ v2_funct_1(C_131)
      | k2_relset_1(A_132,B_130,C_131) != B_130
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_130)))
      | ~ v1_funct_2(C_131,A_132,B_130)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_979,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_969])).

tff(c_990,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_434,c_66,c_979])).

tff(c_992,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_990])).

tff(c_438,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_126])).

tff(c_1006,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_438])).

tff(c_1010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1006])).

tff(c_1012,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_990])).

tff(c_1129,plain,(
    ! [A_133,C_134,B_135] :
      ( k6_partfun1(A_133) = k5_relat_1(C_134,k2_funct_1(C_134))
      | k1_xboole_0 = B_135
      | ~ v2_funct_1(C_134)
      | k2_relset_1(A_133,B_135,C_134) != B_135
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_133,B_135)))
      | ~ v1_funct_2(C_134,A_133,B_135)
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1139,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_1129])).

tff(c_1150,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_434,c_66,c_1139])).

tff(c_1151,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1012,c_1150])).

tff(c_703,plain,(
    ! [C_118,B_119,A_120] :
      ( m1_subset_1(k2_funct_1(C_118),k1_zfmisc_1(k2_zfmisc_1(B_119,A_120)))
      | k2_relset_1(A_120,B_119,C_118) != B_119
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(C_118,A_120,B_119)
      | ~ v1_funct_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_741,plain,(
    ! [C_121,A_122,B_123] :
      ( v1_relat_1(k2_funct_1(C_121))
      | k2_relset_1(A_122,B_123,C_121) != B_123
      | ~ v2_funct_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_2(C_121,A_122,B_123)
      | ~ v1_funct_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_703,c_22])).

tff(c_753,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_741])).

tff(c_762,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_66,c_434,c_753])).

tff(c_550,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_funct_1(k2_funct_1(C_102))
      | k2_relset_1(A_103,B_104,C_102) != B_104
      | ~ v2_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_2(C_102,A_103,B_104)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_553,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_550])).

tff(c_559,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_66,c_434,c_553])).

tff(c_16,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_1011,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_990])).

tff(c_14,plain,(
    ! [B_5,A_3] :
      ( v2_funct_1(B_5)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(k5_relat_1(B_5,A_3))
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1021,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1(k2_relat_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1011,c_14])).

tff(c_1031,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_762,c_559,c_82,c_1021])).

tff(c_1033,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1031])).

tff(c_1036,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1033])).

tff(c_1040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_66,c_1036])).

tff(c_1041,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1031])).

tff(c_18,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_338,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80),k2_relat_1(A_80))))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_26,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_399,plain,(
    ! [A_82] :
      ( v4_relat_1(A_82,k1_relat_1(A_82))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_338,c_26])).

tff(c_30,plain,(
    ! [B_20] :
      ( v1_partfun1(B_20,k1_relat_1(B_20))
      | ~ v4_relat_1(B_20,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_412,plain,(
    ! [A_83] :
      ( v1_partfun1(A_83,k1_relat_1(A_83))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_399,c_30])).

tff(c_415,plain,(
    ! [A_6] :
      ( v1_partfun1(k2_funct_1(A_6),k2_relat_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_412])).

tff(c_764,plain,(
    ! [C_124,B_125,A_126] :
      ( v4_relat_1(k2_funct_1(C_124),B_125)
      | k2_relset_1(A_126,B_125,C_124) != B_125
      | ~ v2_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2(C_124,A_126,B_125)
      | ~ v1_funct_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_703,c_26])).

tff(c_776,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_764])).

tff(c_785,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_66,c_434,c_776])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(B_20) = A_19
      | ~ v1_partfun1(B_20,A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_789,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_785,c_32])).

tff(c_792,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_789])).

tff(c_793,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_792])).

tff(c_814,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_415,c_793])).

tff(c_818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_66,c_762,c_559,c_814])).

tff(c_819,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_792])).

tff(c_1042,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1031])).

tff(c_20,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k2_relat_1(A_7)) != k5_relat_1(B_9,A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_81,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_partfun1(k2_relat_1(A_7)) != k5_relat_1(B_9,A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_20])).

tff(c_1053,plain,(
    ! [B_9] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_9
      | k5_relat_1(B_9,k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_9) != k1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_81])).

tff(c_2037,plain,(
    ! [B_155] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_155
      | k5_relat_1(B_155,k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_155) != k2_relat_1('#skF_3')
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_559,c_1041,c_819,c_1053])).

tff(c_2043,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_2037])).

tff(c_2050,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_2043])).

tff(c_596,plain,(
    ! [C_107,B_108,A_109] :
      ( v1_funct_2(k2_funct_1(C_107),B_108,A_109)
      | k2_relset_1(A_109,B_108,C_107) != B_108
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_2(C_107,A_109,B_108)
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_602,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_596])).

tff(c_609,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_66,c_434,c_602])).

tff(c_52,plain,(
    ! [A_35] :
      ( m1_subset_1(A_35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35))))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_478,plain,(
    ! [A_87] :
      ( k2_relset_1(k1_relat_1(A_87),k2_relat_1(A_87),A_87) = k2_relat_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_52,c_420])).

tff(c_496,plain,(
    ! [A_6] :
      ( k2_relset_1(k2_relat_1(A_6),k2_relat_1(k2_funct_1(A_6)),k2_funct_1(A_6)) = k2_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_478])).

tff(c_1051,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_496])).

tff(c_1095,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_66,c_762,c_559,c_1042,c_1051])).

tff(c_664,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_tops_2(A_114,B_115,C_116) = k2_funct_1(C_116)
      | ~ v2_funct_1(C_116)
      | k2_relset_1(A_114,B_115,C_116) != B_115
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_2(C_116,A_114,B_115)
      | ~ v1_funct_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1751,plain,(
    ! [A_149] :
      ( k2_tops_2(k1_relat_1(A_149),k2_relat_1(A_149),A_149) = k2_funct_1(A_149)
      | ~ v2_funct_1(A_149)
      | k2_relset_1(k1_relat_1(A_149),k2_relat_1(A_149),A_149) != k2_relat_1(A_149)
      | ~ v1_funct_2(A_149,k1_relat_1(A_149),k2_relat_1(A_149))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_52,c_664])).

tff(c_1760,plain,
    ( k2_tops_2(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) != k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_1751])).

tff(c_1781,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_559,c_609,c_819,c_1095,c_819,c_1042,c_1042,c_1041,c_819,c_1042,c_1760])).

tff(c_673,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_664])).

tff(c_681,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_435,c_434,c_66,c_673])).

tff(c_64,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_151,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_103,c_102,c_102,c_102,c_64])).

tff(c_327,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_325,c_325,c_151])).

tff(c_529,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_429,c_429,c_327])).

tff(c_683,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_529])).

tff(c_1788,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_683])).

tff(c_2057,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2050,c_1788])).

tff(c_2078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1257,c_2057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.91  
% 4.84/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.91  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.84/1.91  
% 4.84/1.91  %Foreground sorts:
% 4.84/1.91  
% 4.84/1.91  
% 4.84/1.91  %Background operators:
% 4.84/1.91  
% 4.84/1.91  
% 4.84/1.91  %Foreground operators:
% 4.84/1.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.84/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.84/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.84/1.91  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.84/1.91  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.84/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.84/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.84/1.91  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.84/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.84/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.84/1.91  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.84/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.84/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.84/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.84/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.84/1.91  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.84/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.84/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/1.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.84/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.84/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.84/1.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.84/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.84/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.84/1.91  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.84/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/1.91  
% 5.24/1.94  tff(f_225, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 5.24/1.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.24/1.94  tff(f_183, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.24/1.94  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.24/1.94  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.24/1.94  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.24/1.94  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.24/1.94  tff(f_137, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 5.24/1.94  tff(f_191, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.24/1.94  tff(f_120, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 5.24/1.94  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 5.24/1.94  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.24/1.94  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.24/1.94  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.24/1.94  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.24/1.94  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 5.24/1.94  tff(f_179, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.24/1.94  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 5.24/1.94  tff(f_203, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.24/1.94  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.24/1.94  tff(c_80, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_95, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.24/1.94  tff(c_103, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_95])).
% 5.24/1.94  tff(c_76, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_102, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_95])).
% 5.24/1.94  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_135, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_102, c_70])).
% 5.24/1.94  tff(c_22, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.24/1.94  tff(c_139, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_22])).
% 5.24/1.94  tff(c_145, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.24/1.94  tff(c_149, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_135, c_145])).
% 5.24/1.94  tff(c_180, plain, (![B_65, A_66]: (k1_relat_1(B_65)=A_66 | ~v1_partfun1(B_65, A_66) | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.24/1.94  tff(c_183, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_149, c_180])).
% 5.24/1.94  tff(c_186, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_183])).
% 5.24/1.94  tff(c_187, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_186])).
% 5.24/1.94  tff(c_224, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.94  tff(c_232, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_224])).
% 5.24/1.94  tff(c_68, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_128, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_102, c_68])).
% 5.24/1.94  tff(c_237, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_128])).
% 5.24/1.94  tff(c_72, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_104, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_72])).
% 5.24/1.94  tff(c_113, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_104])).
% 5.24/1.94  tff(c_247, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_113])).
% 5.24/1.94  tff(c_245, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_135])).
% 5.24/1.94  tff(c_303, plain, (![B_77, C_78, A_79]: (k1_xboole_0=B_77 | v1_partfun1(C_78, A_79) | ~v1_funct_2(C_78, A_79, B_77) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_77))) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.24/1.94  tff(c_306, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_245, c_303])).
% 5.24/1.94  tff(c_312, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_247, c_306])).
% 5.24/1.94  tff(c_313, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_187, c_312])).
% 5.24/1.94  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_115, plain, (![A_50]: (~v1_xboole_0(u1_struct_0(A_50)) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.24/1.94  tff(c_121, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102, c_115])).
% 5.24/1.94  tff(c_125, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_121])).
% 5.24/1.94  tff(c_126, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_125])).
% 5.24/1.94  tff(c_246, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_126])).
% 5.24/1.94  tff(c_320, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_246])).
% 5.24/1.94  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_320])).
% 5.24/1.94  tff(c_325, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_186])).
% 5.24/1.94  tff(c_329, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_135])).
% 5.24/1.94  tff(c_420, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.94  tff(c_427, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_329, c_420])).
% 5.24/1.94  tff(c_330, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_128])).
% 5.24/1.94  tff(c_429, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_330])).
% 5.24/1.94  tff(c_332, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_113])).
% 5.24/1.94  tff(c_435, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_332])).
% 5.24/1.94  tff(c_436, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_329])).
% 5.24/1.94  tff(c_1194, plain, (![A_136, B_137, C_138, D_139]: (r2_funct_2(A_136, B_137, C_138, C_138) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_2(D_139, A_136, B_137) | ~v1_funct_1(D_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_2(C_138, A_136, B_137) | ~v1_funct_1(C_138))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.24/1.94  tff(c_1204, plain, (![C_138]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_138, C_138) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_138, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_138))), inference(resolution, [status(thm)], [c_436, c_1194])).
% 5.24/1.94  tff(c_1245, plain, (![C_140]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_140, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_140, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_140))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_1204])).
% 5.24/1.94  tff(c_1250, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_1245])).
% 5.24/1.94  tff(c_1257, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_1250])).
% 5.24/1.94  tff(c_434, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_427])).
% 5.24/1.94  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_969, plain, (![B_130, C_131, A_132]: (k6_partfun1(B_130)=k5_relat_1(k2_funct_1(C_131), C_131) | k1_xboole_0=B_130 | ~v2_funct_1(C_131) | k2_relset_1(A_132, B_130, C_131)!=B_130 | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_130))) | ~v1_funct_2(C_131, A_132, B_130) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.24/1.94  tff(c_979, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_969])).
% 5.24/1.94  tff(c_990, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_434, c_66, c_979])).
% 5.24/1.94  tff(c_992, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_990])).
% 5.24/1.94  tff(c_438, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_126])).
% 5.24/1.94  tff(c_1006, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_992, c_438])).
% 5.24/1.94  tff(c_1010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1006])).
% 5.24/1.94  tff(c_1012, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_990])).
% 5.24/1.94  tff(c_1129, plain, (![A_133, C_134, B_135]: (k6_partfun1(A_133)=k5_relat_1(C_134, k2_funct_1(C_134)) | k1_xboole_0=B_135 | ~v2_funct_1(C_134) | k2_relset_1(A_133, B_135, C_134)!=B_135 | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_133, B_135))) | ~v1_funct_2(C_134, A_133, B_135) | ~v1_funct_1(C_134))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.24/1.94  tff(c_1139, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_1129])).
% 5.24/1.94  tff(c_1150, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_434, c_66, c_1139])).
% 5.24/1.94  tff(c_1151, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1012, c_1150])).
% 5.24/1.94  tff(c_703, plain, (![C_118, B_119, A_120]: (m1_subset_1(k2_funct_1(C_118), k1_zfmisc_1(k2_zfmisc_1(B_119, A_120))) | k2_relset_1(A_120, B_119, C_118)!=B_119 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(C_118, A_120, B_119) | ~v1_funct_1(C_118))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.24/1.94  tff(c_741, plain, (![C_121, A_122, B_123]: (v1_relat_1(k2_funct_1(C_121)) | k2_relset_1(A_122, B_123, C_121)!=B_123 | ~v2_funct_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_2(C_121, A_122, B_123) | ~v1_funct_1(C_121))), inference(resolution, [status(thm)], [c_703, c_22])).
% 5.24/1.94  tff(c_753, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_741])).
% 5.24/1.94  tff(c_762, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_66, c_434, c_753])).
% 5.24/1.94  tff(c_550, plain, (![C_102, A_103, B_104]: (v1_funct_1(k2_funct_1(C_102)) | k2_relset_1(A_103, B_104, C_102)!=B_104 | ~v2_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_2(C_102, A_103, B_104) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.24/1.94  tff(c_553, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_550])).
% 5.24/1.94  tff(c_559, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_66, c_434, c_553])).
% 5.24/1.94  tff(c_16, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.24/1.94  tff(c_34, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.24/1.94  tff(c_10, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.24/1.94  tff(c_82, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 5.24/1.94  tff(c_1011, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_990])).
% 5.24/1.94  tff(c_14, plain, (![B_5, A_3]: (v2_funct_1(B_5) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(k5_relat_1(B_5, A_3)) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.24/1.94  tff(c_1021, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k6_partfun1(k2_relat_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1011, c_14])).
% 5.24/1.94  tff(c_1031, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_762, c_559, c_82, c_1021])).
% 5.24/1.94  tff(c_1033, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1031])).
% 5.24/1.94  tff(c_1036, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1033])).
% 5.24/1.94  tff(c_1040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_66, c_1036])).
% 5.24/1.94  tff(c_1041, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1031])).
% 5.24/1.94  tff(c_18, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.24/1.94  tff(c_338, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80), k2_relat_1(A_80)))) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.24/1.94  tff(c_26, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.24/1.94  tff(c_399, plain, (![A_82]: (v4_relat_1(A_82, k1_relat_1(A_82)) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_338, c_26])).
% 5.24/1.94  tff(c_30, plain, (![B_20]: (v1_partfun1(B_20, k1_relat_1(B_20)) | ~v4_relat_1(B_20, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.24/1.94  tff(c_412, plain, (![A_83]: (v1_partfun1(A_83, k1_relat_1(A_83)) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_399, c_30])).
% 5.24/1.94  tff(c_415, plain, (![A_6]: (v1_partfun1(k2_funct_1(A_6), k2_relat_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_18, c_412])).
% 5.24/1.94  tff(c_764, plain, (![C_124, B_125, A_126]: (v4_relat_1(k2_funct_1(C_124), B_125) | k2_relset_1(A_126, B_125, C_124)!=B_125 | ~v2_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2(C_124, A_126, B_125) | ~v1_funct_1(C_124))), inference(resolution, [status(thm)], [c_703, c_26])).
% 5.24/1.94  tff(c_776, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_764])).
% 5.24/1.94  tff(c_785, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_66, c_434, c_776])).
% 5.24/1.94  tff(c_32, plain, (![B_20, A_19]: (k1_relat_1(B_20)=A_19 | ~v1_partfun1(B_20, A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.24/1.94  tff(c_789, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_785, c_32])).
% 5.24/1.94  tff(c_792, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_789])).
% 5.24/1.94  tff(c_793, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_792])).
% 5.24/1.94  tff(c_814, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_415, c_793])).
% 5.24/1.94  tff(c_818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_66, c_762, c_559, c_814])).
% 5.24/1.94  tff(c_819, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_792])).
% 5.24/1.94  tff(c_1042, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1031])).
% 5.24/1.94  tff(c_20, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k2_relat_1(A_7))!=k5_relat_1(B_9, A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.24/1.94  tff(c_81, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_partfun1(k2_relat_1(A_7))!=k5_relat_1(B_9, A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_20])).
% 5.24/1.94  tff(c_1053, plain, (![B_9]: (k2_funct_1(k2_funct_1('#skF_3'))=B_9 | k5_relat_1(B_9, k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1(B_9)!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_81])).
% 5.24/1.94  tff(c_2037, plain, (![B_155]: (k2_funct_1(k2_funct_1('#skF_3'))=B_155 | k5_relat_1(B_155, k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1(B_155)!=k2_relat_1('#skF_3') | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_559, c_1041, c_819, c_1053])).
% 5.24/1.94  tff(c_2043, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1151, c_2037])).
% 5.24/1.94  tff(c_2050, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_2043])).
% 5.24/1.94  tff(c_596, plain, (![C_107, B_108, A_109]: (v1_funct_2(k2_funct_1(C_107), B_108, A_109) | k2_relset_1(A_109, B_108, C_107)!=B_108 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_2(C_107, A_109, B_108) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.24/1.94  tff(c_602, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_596])).
% 5.24/1.94  tff(c_609, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_66, c_434, c_602])).
% 5.24/1.94  tff(c_52, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35)))) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.24/1.94  tff(c_478, plain, (![A_87]: (k2_relset_1(k1_relat_1(A_87), k2_relat_1(A_87), A_87)=k2_relat_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_52, c_420])).
% 5.24/1.94  tff(c_496, plain, (![A_6]: (k2_relset_1(k2_relat_1(A_6), k2_relat_1(k2_funct_1(A_6)), k2_funct_1(A_6))=k2_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_18, c_478])).
% 5.24/1.94  tff(c_1051, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1042, c_496])).
% 5.24/1.94  tff(c_1095, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_66, c_762, c_559, c_1042, c_1051])).
% 5.24/1.94  tff(c_664, plain, (![A_114, B_115, C_116]: (k2_tops_2(A_114, B_115, C_116)=k2_funct_1(C_116) | ~v2_funct_1(C_116) | k2_relset_1(A_114, B_115, C_116)!=B_115 | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_2(C_116, A_114, B_115) | ~v1_funct_1(C_116))), inference(cnfTransformation, [status(thm)], [f_203])).
% 5.24/1.94  tff(c_1751, plain, (![A_149]: (k2_tops_2(k1_relat_1(A_149), k2_relat_1(A_149), A_149)=k2_funct_1(A_149) | ~v2_funct_1(A_149) | k2_relset_1(k1_relat_1(A_149), k2_relat_1(A_149), A_149)!=k2_relat_1(A_149) | ~v1_funct_2(A_149, k1_relat_1(A_149), k2_relat_1(A_149)) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_52, c_664])).
% 5.24/1.94  tff(c_1760, plain, (k2_tops_2(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))!=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_1751])).
% 5.24/1.94  tff(c_1781, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_559, c_609, c_819, c_1095, c_819, c_1042, c_1042, c_1041, c_819, c_1042, c_1760])).
% 5.24/1.94  tff(c_673, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_664])).
% 5.24/1.94  tff(c_681, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_435, c_434, c_66, c_673])).
% 5.24/1.94  tff(c_64, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.24/1.94  tff(c_151, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_103, c_102, c_102, c_102, c_64])).
% 5.24/1.94  tff(c_327, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_325, c_325, c_151])).
% 5.24/1.94  tff(c_529, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_429, c_429, c_327])).
% 5.24/1.94  tff(c_683, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_529])).
% 5.24/1.94  tff(c_1788, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_683])).
% 5.24/1.94  tff(c_2057, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2050, c_1788])).
% 5.24/1.94  tff(c_2078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1257, c_2057])).
% 5.24/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.94  
% 5.24/1.94  Inference rules
% 5.24/1.94  ----------------------
% 5.24/1.94  #Ref     : 0
% 5.24/1.94  #Sup     : 404
% 5.24/1.94  #Fact    : 0
% 5.24/1.94  #Define  : 0
% 5.24/1.94  #Split   : 11
% 5.24/1.94  #Chain   : 0
% 5.24/1.94  #Close   : 0
% 5.24/1.94  
% 5.24/1.94  Ordering : KBO
% 5.24/1.94  
% 5.24/1.94  Simplification rules
% 5.24/1.94  ----------------------
% 5.24/1.95  #Subsume      : 27
% 5.24/1.95  #Demod        : 985
% 5.24/1.95  #Tautology    : 207
% 5.24/1.95  #SimpNegUnit  : 25
% 5.24/1.95  #BackRed      : 86
% 5.24/1.95  
% 5.24/1.95  #Partial instantiations: 0
% 5.24/1.95  #Strategies tried      : 1
% 5.24/1.95  
% 5.24/1.95  Timing (in seconds)
% 5.24/1.95  ----------------------
% 5.24/1.95  Preprocessing        : 0.38
% 5.24/1.95  Parsing              : 0.20
% 5.24/1.95  CNF conversion       : 0.03
% 5.24/1.95  Main loop            : 0.71
% 5.24/1.95  Inferencing          : 0.23
% 5.24/1.95  Reduction            : 0.27
% 5.24/1.95  Demodulation         : 0.20
% 5.24/1.95  BG Simplification    : 0.04
% 5.24/1.95  Subsumption          : 0.12
% 5.24/1.95  Abstraction          : 0.04
% 5.24/1.95  MUC search           : 0.00
% 5.24/1.95  Cooper               : 0.00
% 5.24/1.95  Total                : 1.16
% 5.24/1.95  Index Insertion      : 0.00
% 5.24/1.95  Index Deletion       : 0.00
% 5.24/1.95  Index Matching       : 0.00
% 5.24/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
