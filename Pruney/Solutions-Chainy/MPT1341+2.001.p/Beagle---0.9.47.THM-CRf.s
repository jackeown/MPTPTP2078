%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:46 EST 2020

% Result     : Theorem 6.35s
% Output     : CNFRefutation 6.65s
% Verified   : 
% Statistics : Number of formulae       :  168 (2516 expanded)
%              Number of leaves         :   46 ( 945 expanded)
%              Depth                    :   15
%              Number of atoms          :  393 (8280 expanded)
%              Number of equality atoms :  140 (3131 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(A),C,k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k6_partfun1(k1_relset_1(u1_struct_0(A),u1_struct_0(B),C))
                    & k1_partfun1(u1_struct_0(B),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),C) = k6_partfun1(k2_relset_1(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_101,axiom,(
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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_117,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_64,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_80,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_88,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_80])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_87,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_80])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_93,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_58])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_93])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_139,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_87,c_56])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_134,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_87,c_54])).

tff(c_3589,plain,(
    ! [C_603,A_604,B_605] :
      ( v1_funct_1(k2_funct_1(C_603))
      | k2_relset_1(A_604,B_605,C_603) != B_605
      | ~ v2_funct_1(C_603)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_604,B_605)))
      | ~ v1_funct_2(C_603,A_604,B_605)
      | ~ v1_funct_1(C_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3592,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_3589])).

tff(c_3603,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_52,c_134,c_3592])).

tff(c_24,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_146,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_24])).

tff(c_4219,plain,(
    ! [A_699,C_700,B_701] :
      ( k6_partfun1(A_699) = k5_relat_1(C_700,k2_funct_1(C_700))
      | k1_xboole_0 = B_701
      | ~ v2_funct_1(C_700)
      | k2_relset_1(A_699,B_701,C_700) != B_701
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(A_699,B_701)))
      | ~ v1_funct_2(C_700,A_699,B_701)
      | ~ v1_funct_1(C_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4223,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_4219])).

tff(c_4233,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_134,c_52,c_4223])).

tff(c_4236,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4233])).

tff(c_3171,plain,(
    ! [C_528,B_529,A_530] :
      ( v5_relat_1(C_528,B_529)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_530,B_529))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3183,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_139,c_3171])).

tff(c_4247,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_3183])).

tff(c_3140,plain,(
    ! [B_522,A_523] :
      ( r1_tarski(k2_relat_1(B_522),A_523)
      | ~ v5_relat_1(B_522,A_523)
      | ~ v1_relat_1(B_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_100])).

tff(c_153,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_108,c_153])).

tff(c_3156,plain,(
    ! [B_522] :
      ( k2_relat_1(B_522) = k1_xboole_0
      | ~ v5_relat_1(B_522,k1_xboole_0)
      | ~ v1_relat_1(B_522) ) ),
    inference(resolution,[status(thm)],[c_3140,c_161])).

tff(c_4260,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4247,c_3156])).

tff(c_4263,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_4260])).

tff(c_34,plain,(
    ! [A_27] : k6_relat_1(A_27) = k6_partfun1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_partfun1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_20])).

tff(c_4252,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_94])).

tff(c_4251,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_4236,c_134])).

tff(c_4250,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_139])).

tff(c_4064,plain,(
    ! [C_675,B_676,A_677] :
      ( m1_subset_1(k2_funct_1(C_675),k1_zfmisc_1(k2_zfmisc_1(B_676,A_677)))
      | k2_relset_1(A_677,B_676,C_675) != B_676
      | ~ v2_funct_1(C_675)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(k2_zfmisc_1(A_677,B_676)))
      | ~ v1_funct_2(C_675,A_677,B_676)
      | ~ v1_funct_1(C_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3837,plain,(
    ! [B_645,A_641,F_644,E_646,D_642,C_643] :
      ( k1_partfun1(A_641,B_645,C_643,D_642,E_646,F_644) = k5_relat_1(E_646,F_644)
      | ~ m1_subset_1(F_644,k1_zfmisc_1(k2_zfmisc_1(C_643,D_642)))
      | ~ v1_funct_1(F_644)
      | ~ m1_subset_1(E_646,k1_zfmisc_1(k2_zfmisc_1(A_641,B_645)))
      | ~ v1_funct_1(E_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3839,plain,(
    ! [A_641,B_645,E_646] :
      ( k1_partfun1(A_641,B_645,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),E_646,'#skF_3') = k5_relat_1(E_646,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_646,k1_zfmisc_1(k2_zfmisc_1(A_641,B_645)))
      | ~ v1_funct_1(E_646) ) ),
    inference(resolution,[status(thm)],[c_139,c_3837])).

tff(c_3848,plain,(
    ! [A_641,B_645,E_646] :
      ( k1_partfun1(A_641,B_645,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),E_646,'#skF_3') = k5_relat_1(E_646,'#skF_3')
      | ~ m1_subset_1(E_646,k1_zfmisc_1(k2_zfmisc_1(A_641,B_645)))
      | ~ v1_funct_1(E_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3839])).

tff(c_4096,plain,(
    ! [B_676,A_677,C_675] :
      ( k1_partfun1(B_676,A_677,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(C_675),'#skF_3') = k5_relat_1(k2_funct_1(C_675),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_675))
      | k2_relset_1(A_677,B_676,C_675) != B_676
      | ~ v2_funct_1(C_675)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(k2_zfmisc_1(A_677,B_676)))
      | ~ v1_funct_2(C_675,A_677,B_676)
      | ~ v1_funct_1(C_675) ) ),
    inference(resolution,[status(thm)],[c_4064,c_3848])).

tff(c_4607,plain,(
    ! [B_735,A_736,C_737] :
      ( k1_partfun1(B_735,A_736,k2_struct_0('#skF_1'),k1_xboole_0,k2_funct_1(C_737),'#skF_3') = k5_relat_1(k2_funct_1(C_737),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_737))
      | k2_relset_1(A_736,B_735,C_737) != B_735
      | ~ v2_funct_1(C_737)
      | ~ m1_subset_1(C_737,k1_zfmisc_1(k2_zfmisc_1(A_736,B_735)))
      | ~ v1_funct_2(C_737,A_736,B_735)
      | ~ v1_funct_1(C_737) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_4096])).

tff(c_4610,plain,
    ( k1_partfun1(k1_xboole_0,k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4250,c_4607])).

tff(c_4624,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4252,c_52,c_4251,c_3603,c_4610])).

tff(c_3745,plain,(
    ! [A_635,B_636,C_637] :
      ( k2_tops_2(A_635,B_636,C_637) = k2_funct_1(C_637)
      | ~ v2_funct_1(C_637)
      | k2_relset_1(A_635,B_636,C_637) != B_636
      | ~ m1_subset_1(C_637,k1_zfmisc_1(k2_zfmisc_1(A_635,B_636)))
      | ~ v1_funct_2(C_637,A_635,B_636)
      | ~ v1_funct_1(C_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3748,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_3745])).

tff(c_3759,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_134,c_52,c_3748])).

tff(c_1131,plain,(
    ! [C_224,B_225,A_226] :
      ( m1_subset_1(k2_funct_1(C_224),k1_zfmisc_1(k2_zfmisc_1(B_225,A_226)))
      | k2_relset_1(A_226,B_225,C_224) != B_225
      | ~ v2_funct_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225)))
      | ~ v1_funct_2(C_224,A_226,B_225)
      | ~ v1_funct_1(C_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1173,plain,(
    ! [C_224,B_225,A_226] :
      ( r1_tarski(k2_funct_1(C_224),k2_zfmisc_1(B_225,A_226))
      | k2_relset_1(A_226,B_225,C_224) != B_225
      | ~ v2_funct_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225)))
      | ~ v1_funct_2(C_224,A_226,B_225)
      | ~ v1_funct_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_1131,c_10])).

tff(c_652,plain,(
    ! [C_151,A_152,B_153] :
      ( v1_funct_1(k2_funct_1(C_151))
      | k2_relset_1(A_152,B_153,C_151) != B_153
      | ~ v2_funct_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_2(C_151,A_152,B_153)
      | ~ v1_funct_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_655,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_652])).

tff(c_666,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_52,c_134,c_655])).

tff(c_22,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_partfun1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22])).

tff(c_1322,plain,(
    ! [B_262,C_263,A_264] :
      ( k6_partfun1(B_262) = k5_relat_1(k2_funct_1(C_263),C_263)
      | k1_xboole_0 = B_262
      | ~ v2_funct_1(C_263)
      | k2_relset_1(A_264,B_262,C_263) != B_262
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_264,B_262)))
      | ~ v1_funct_2(C_263,A_264,B_262)
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1326,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_1322])).

tff(c_1336,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_134,c_52,c_1326])).

tff(c_1339,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1336])).

tff(c_1353,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_94])).

tff(c_1352,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_1339,c_134])).

tff(c_1351,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_139])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_904,plain,(
    ! [B_194,A_190,E_195,F_193,D_191,C_192] :
      ( k1_partfun1(A_190,B_194,C_192,D_191,E_195,F_193) = k5_relat_1(E_195,F_193)
      | ~ m1_subset_1(F_193,k1_zfmisc_1(k2_zfmisc_1(C_192,D_191)))
      | ~ v1_funct_1(F_193)
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2257,plain,(
    ! [C_378,A_381,D_377,A_379,E_380,B_376] :
      ( k1_partfun1(A_379,B_376,C_378,D_377,E_380,A_381) = k5_relat_1(E_380,A_381)
      | ~ v1_funct_1(A_381)
      | ~ m1_subset_1(E_380,k1_zfmisc_1(k2_zfmisc_1(A_379,B_376)))
      | ~ v1_funct_1(E_380)
      | ~ r1_tarski(A_381,k2_zfmisc_1(C_378,D_377)) ) ),
    inference(resolution,[status(thm)],[c_12,c_904])).

tff(c_2259,plain,(
    ! [C_378,D_377,A_381] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k1_xboole_0,C_378,D_377,'#skF_3',A_381) = k5_relat_1('#skF_3',A_381)
      | ~ v1_funct_1(A_381)
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(A_381,k2_zfmisc_1(C_378,D_377)) ) ),
    inference(resolution,[status(thm)],[c_1351,c_2257])).

tff(c_2274,plain,(
    ! [C_382,D_383,A_384] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k1_xboole_0,C_382,D_383,'#skF_3',A_384) = k5_relat_1('#skF_3',A_384)
      | ~ v1_funct_1(A_384)
      | ~ r1_tarski(A_384,k2_zfmisc_1(C_382,D_383)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2259])).

tff(c_2408,plain,(
    ! [B_413,A_414,C_415] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k1_xboole_0,B_413,A_414,'#skF_3',k2_funct_1(C_415)) = k5_relat_1('#skF_3',k2_funct_1(C_415))
      | ~ v1_funct_1(k2_funct_1(C_415))
      | k2_relset_1(A_414,B_413,C_415) != B_413
      | ~ v2_funct_1(C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_414,B_413)))
      | ~ v1_funct_2(C_415,A_414,B_413)
      | ~ v1_funct_1(C_415) ) ),
    inference(resolution,[status(thm)],[c_1173,c_2274])).

tff(c_2411,plain,
    ( k1_partfun1(k2_struct_0('#skF_1'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1351,c_2408])).

tff(c_2425,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1353,c_52,c_1352,c_666,c_2411])).

tff(c_789,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_tops_2(A_179,B_180,C_181) = k2_funct_1(C_181)
      | ~ v2_funct_1(C_181)
      | k2_relset_1(A_179,B_180,C_181) != B_180
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(C_181,A_179,B_180)
      | ~ v1_funct_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_792,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_789])).

tff(c_803,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_134,c_52,c_792])).

tff(c_468,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_480,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_468])).

tff(c_50,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_65,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50])).

tff(c_212,plain,
    ( k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_88,c_88,c_87,c_87,c_87,c_87,c_88,c_88,c_88,c_87,c_87,c_87,c_65])).

tff(c_213,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_495,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_213])).

tff(c_806,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_495])).

tff(c_1343,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_1339,c_806])).

tff(c_2429,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_1343])).

tff(c_2436,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2429])).

tff(c_2440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_52,c_2436])).

tff(c_2442,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1336])).

tff(c_2462,plain,(
    ! [A_416,C_417,B_418] :
      ( k6_partfun1(A_416) = k5_relat_1(C_417,k2_funct_1(C_417))
      | k1_xboole_0 = B_418
      | ~ v2_funct_1(C_417)
      | k2_relset_1(A_416,B_418,C_417) != B_418
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_416,B_418)))
      | ~ v1_funct_2(C_417,A_416,B_418)
      | ~ v1_funct_1(C_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2466,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_2462])).

tff(c_2476,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_134,c_52,c_2466])).

tff(c_2477,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_2442,c_2476])).

tff(c_2484,plain,
    ( k6_partfun1(k2_struct_0('#skF_1')) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2477,c_66])).

tff(c_2491,plain,(
    k6_partfun1(k2_struct_0('#skF_1')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_52,c_2484])).

tff(c_2495,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2491,c_2477])).

tff(c_3072,plain,(
    ! [C_513,B_511,A_516,E_515,A_514,D_512] :
      ( k1_partfun1(A_514,B_511,C_513,D_512,E_515,A_516) = k5_relat_1(E_515,A_516)
      | ~ v1_funct_1(A_516)
      | ~ m1_subset_1(E_515,k1_zfmisc_1(k2_zfmisc_1(A_514,B_511)))
      | ~ v1_funct_1(E_515)
      | ~ r1_tarski(A_516,k2_zfmisc_1(C_513,D_512)) ) ),
    inference(resolution,[status(thm)],[c_12,c_904])).

tff(c_3076,plain,(
    ! [C_513,D_512,A_516] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_513,D_512,'#skF_3',A_516) = k5_relat_1('#skF_3',A_516)
      | ~ v1_funct_1(A_516)
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(A_516,k2_zfmisc_1(C_513,D_512)) ) ),
    inference(resolution,[status(thm)],[c_139,c_3072])).

tff(c_3089,plain,(
    ! [C_517,D_518,A_519] :
      ( k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_517,D_518,'#skF_3',A_519) = k5_relat_1('#skF_3',A_519)
      | ~ v1_funct_1(A_519)
      | ~ r1_tarski(A_519,k2_zfmisc_1(C_517,D_518)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3076])).

tff(c_3102,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3089,c_806])).

tff(c_3121,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_2495,c_3102])).

tff(c_3131,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1173,c_3121])).

tff(c_3135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_139,c_52,c_134,c_3131])).

tff(c_3136,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_3763,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3759,c_3136])).

tff(c_4241,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_4236,c_4236,c_3763])).

tff(c_4628,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4624,c_4241])).

tff(c_4635,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1(k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_4628])).

tff(c_4638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_52,c_4263,c_4635])).

tff(c_4640,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4233])).

tff(c_4660,plain,(
    ! [B_738,C_739,A_740] :
      ( k6_partfun1(B_738) = k5_relat_1(k2_funct_1(C_739),C_739)
      | k1_xboole_0 = B_738
      | ~ v2_funct_1(C_739)
      | k2_relset_1(A_740,B_738,C_739) != B_738
      | ~ m1_subset_1(C_739,k1_zfmisc_1(k2_zfmisc_1(A_740,B_738)))
      | ~ v1_funct_2(C_739,A_740,B_738)
      | ~ v1_funct_1(C_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4664,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_4660])).

tff(c_4674,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_134,c_52,c_4664])).

tff(c_4675,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_4640,c_4674])).

tff(c_4682,plain,
    ( k6_partfun1(k2_struct_0('#skF_2')) = k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4675,c_67])).

tff(c_4689,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_60,c_52,c_4682])).

tff(c_4693,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4689,c_4675])).

tff(c_4694,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4689,c_3763])).

tff(c_4752,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4096,c_4694])).

tff(c_4758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_139,c_52,c_134,c_3603,c_4693,c_4752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.35/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.38  
% 6.35/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.35/2.38  
% 6.35/2.38  %Foreground sorts:
% 6.35/2.38  
% 6.35/2.38  
% 6.35/2.38  %Background operators:
% 6.35/2.38  
% 6.35/2.38  
% 6.35/2.38  %Foreground operators:
% 6.35/2.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.35/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.35/2.38  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.35/2.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.35/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.35/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.35/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.35/2.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.35/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.35/2.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.35/2.38  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.35/2.38  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.35/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.35/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.35/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.35/2.38  tff('#skF_1', type, '#skF_1': $i).
% 6.35/2.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.35/2.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.35/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.35/2.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.35/2.38  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.35/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.35/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.35/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.35/2.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.35/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.35/2.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.35/2.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.35/2.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.35/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.35/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.35/2.38  
% 6.65/2.41  tff(f_154, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_partfun1(u1_struct_0(A), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), C, k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k6_partfun1(k1_relset_1(u1_struct_0(A), u1_struct_0(B), C))) & (k1_partfun1(u1_struct_0(B), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), C) = k6_partfun1(k2_relset_1(u1_struct_0(A), u1_struct_0(B), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_2)).
% 6.65/2.41  tff(f_121, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.65/2.41  tff(f_101, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.65/2.41  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.65/2.41  tff(f_117, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.65/2.41  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.65/2.41  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.65/2.41  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.65/2.41  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.65/2.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.65/2.41  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.65/2.41  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.65/2.41  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.65/2.41  tff(f_133, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 6.65/2.41  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.65/2.41  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_64, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_80, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.65/2.41  tff(c_88, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_80])).
% 6.65/2.41  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_87, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_80])).
% 6.65/2.41  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_93, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_58])).
% 6.65/2.41  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_93])).
% 6.65/2.41  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_139, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_87, c_56])).
% 6.65/2.41  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_134, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_87, c_54])).
% 6.65/2.41  tff(c_3589, plain, (![C_603, A_604, B_605]: (v1_funct_1(k2_funct_1(C_603)) | k2_relset_1(A_604, B_605, C_603)!=B_605 | ~v2_funct_1(C_603) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_604, B_605))) | ~v1_funct_2(C_603, A_604, B_605) | ~v1_funct_1(C_603))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.65/2.41  tff(c_3592, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_3589])).
% 6.65/2.41  tff(c_3603, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_52, c_134, c_3592])).
% 6.65/2.41  tff(c_24, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.65/2.41  tff(c_146, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_24])).
% 6.65/2.41  tff(c_4219, plain, (![A_699, C_700, B_701]: (k6_partfun1(A_699)=k5_relat_1(C_700, k2_funct_1(C_700)) | k1_xboole_0=B_701 | ~v2_funct_1(C_700) | k2_relset_1(A_699, B_701, C_700)!=B_701 | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(A_699, B_701))) | ~v1_funct_2(C_700, A_699, B_701) | ~v1_funct_1(C_700))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.65/2.41  tff(c_4223, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_4219])).
% 6.65/2.41  tff(c_4233, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_134, c_52, c_4223])).
% 6.65/2.41  tff(c_4236, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4233])).
% 6.65/2.41  tff(c_3171, plain, (![C_528, B_529, A_530]: (v5_relat_1(C_528, B_529) | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_530, B_529))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.65/2.41  tff(c_3183, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_139, c_3171])).
% 6.65/2.41  tff(c_4247, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_3183])).
% 6.65/2.41  tff(c_3140, plain, (![B_522, A_523]: (r1_tarski(k2_relat_1(B_522), A_523) | ~v5_relat_1(B_522, A_523) | ~v1_relat_1(B_522))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.65/2.41  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.65/2.41  tff(c_100, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.65/2.41  tff(c_108, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_100])).
% 6.65/2.41  tff(c_153, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.65/2.41  tff(c_161, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_108, c_153])).
% 6.65/2.41  tff(c_3156, plain, (![B_522]: (k2_relat_1(B_522)=k1_xboole_0 | ~v5_relat_1(B_522, k1_xboole_0) | ~v1_relat_1(B_522))), inference(resolution, [status(thm)], [c_3140, c_161])).
% 6.65/2.41  tff(c_4260, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4247, c_3156])).
% 6.65/2.41  tff(c_4263, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_146, c_4260])).
% 6.65/2.41  tff(c_34, plain, (![A_27]: (k6_relat_1(A_27)=k6_partfun1(A_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.65/2.41  tff(c_20, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.65/2.41  tff(c_67, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_partfun1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_20])).
% 6.65/2.41  tff(c_4252, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_94])).
% 6.65/2.41  tff(c_4251, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_4236, c_134])).
% 6.65/2.41  tff(c_4250, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_139])).
% 6.65/2.41  tff(c_4064, plain, (![C_675, B_676, A_677]: (m1_subset_1(k2_funct_1(C_675), k1_zfmisc_1(k2_zfmisc_1(B_676, A_677))) | k2_relset_1(A_677, B_676, C_675)!=B_676 | ~v2_funct_1(C_675) | ~m1_subset_1(C_675, k1_zfmisc_1(k2_zfmisc_1(A_677, B_676))) | ~v1_funct_2(C_675, A_677, B_676) | ~v1_funct_1(C_675))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.65/2.41  tff(c_3837, plain, (![B_645, A_641, F_644, E_646, D_642, C_643]: (k1_partfun1(A_641, B_645, C_643, D_642, E_646, F_644)=k5_relat_1(E_646, F_644) | ~m1_subset_1(F_644, k1_zfmisc_1(k2_zfmisc_1(C_643, D_642))) | ~v1_funct_1(F_644) | ~m1_subset_1(E_646, k1_zfmisc_1(k2_zfmisc_1(A_641, B_645))) | ~v1_funct_1(E_646))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.65/2.41  tff(c_3839, plain, (![A_641, B_645, E_646]: (k1_partfun1(A_641, B_645, k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), E_646, '#skF_3')=k5_relat_1(E_646, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_646, k1_zfmisc_1(k2_zfmisc_1(A_641, B_645))) | ~v1_funct_1(E_646))), inference(resolution, [status(thm)], [c_139, c_3837])).
% 6.65/2.41  tff(c_3848, plain, (![A_641, B_645, E_646]: (k1_partfun1(A_641, B_645, k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), E_646, '#skF_3')=k5_relat_1(E_646, '#skF_3') | ~m1_subset_1(E_646, k1_zfmisc_1(k2_zfmisc_1(A_641, B_645))) | ~v1_funct_1(E_646))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3839])).
% 6.65/2.41  tff(c_4096, plain, (![B_676, A_677, C_675]: (k1_partfun1(B_676, A_677, k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(C_675), '#skF_3')=k5_relat_1(k2_funct_1(C_675), '#skF_3') | ~v1_funct_1(k2_funct_1(C_675)) | k2_relset_1(A_677, B_676, C_675)!=B_676 | ~v2_funct_1(C_675) | ~m1_subset_1(C_675, k1_zfmisc_1(k2_zfmisc_1(A_677, B_676))) | ~v1_funct_2(C_675, A_677, B_676) | ~v1_funct_1(C_675))), inference(resolution, [status(thm)], [c_4064, c_3848])).
% 6.65/2.41  tff(c_4607, plain, (![B_735, A_736, C_737]: (k1_partfun1(B_735, A_736, k2_struct_0('#skF_1'), k1_xboole_0, k2_funct_1(C_737), '#skF_3')=k5_relat_1(k2_funct_1(C_737), '#skF_3') | ~v1_funct_1(k2_funct_1(C_737)) | k2_relset_1(A_736, B_735, C_737)!=B_735 | ~v2_funct_1(C_737) | ~m1_subset_1(C_737, k1_zfmisc_1(k2_zfmisc_1(A_736, B_735))) | ~v1_funct_2(C_737, A_736, B_735) | ~v1_funct_1(C_737))), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_4096])).
% 6.65/2.41  tff(c_4610, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4250, c_4607])).
% 6.65/2.41  tff(c_4624, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4252, c_52, c_4251, c_3603, c_4610])).
% 6.65/2.41  tff(c_3745, plain, (![A_635, B_636, C_637]: (k2_tops_2(A_635, B_636, C_637)=k2_funct_1(C_637) | ~v2_funct_1(C_637) | k2_relset_1(A_635, B_636, C_637)!=B_636 | ~m1_subset_1(C_637, k1_zfmisc_1(k2_zfmisc_1(A_635, B_636))) | ~v1_funct_2(C_637, A_635, B_636) | ~v1_funct_1(C_637))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.65/2.41  tff(c_3748, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_3745])).
% 6.65/2.41  tff(c_3759, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_134, c_52, c_3748])).
% 6.65/2.41  tff(c_1131, plain, (![C_224, B_225, A_226]: (m1_subset_1(k2_funct_1(C_224), k1_zfmisc_1(k2_zfmisc_1(B_225, A_226))) | k2_relset_1(A_226, B_225, C_224)!=B_225 | ~v2_funct_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))) | ~v1_funct_2(C_224, A_226, B_225) | ~v1_funct_1(C_224))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.65/2.41  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.65/2.41  tff(c_1173, plain, (![C_224, B_225, A_226]: (r1_tarski(k2_funct_1(C_224), k2_zfmisc_1(B_225, A_226)) | k2_relset_1(A_226, B_225, C_224)!=B_225 | ~v2_funct_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))) | ~v1_funct_2(C_224, A_226, B_225) | ~v1_funct_1(C_224))), inference(resolution, [status(thm)], [c_1131, c_10])).
% 6.65/2.41  tff(c_652, plain, (![C_151, A_152, B_153]: (v1_funct_1(k2_funct_1(C_151)) | k2_relset_1(A_152, B_153, C_151)!=B_153 | ~v2_funct_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_2(C_151, A_152, B_153) | ~v1_funct_1(C_151))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.65/2.41  tff(c_655, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_652])).
% 6.65/2.41  tff(c_666, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_52, c_134, c_655])).
% 6.65/2.41  tff(c_22, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.65/2.41  tff(c_66, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_partfun1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_22])).
% 6.65/2.41  tff(c_1322, plain, (![B_262, C_263, A_264]: (k6_partfun1(B_262)=k5_relat_1(k2_funct_1(C_263), C_263) | k1_xboole_0=B_262 | ~v2_funct_1(C_263) | k2_relset_1(A_264, B_262, C_263)!=B_262 | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_264, B_262))) | ~v1_funct_2(C_263, A_264, B_262) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.65/2.41  tff(c_1326, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_1322])).
% 6.65/2.41  tff(c_1336, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_134, c_52, c_1326])).
% 6.65/2.41  tff(c_1339, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1336])).
% 6.65/2.41  tff(c_1353, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_94])).
% 6.65/2.41  tff(c_1352, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_1339, c_134])).
% 6.65/2.41  tff(c_1351, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_139])).
% 6.65/2.41  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.65/2.41  tff(c_904, plain, (![B_194, A_190, E_195, F_193, D_191, C_192]: (k1_partfun1(A_190, B_194, C_192, D_191, E_195, F_193)=k5_relat_1(E_195, F_193) | ~m1_subset_1(F_193, k1_zfmisc_1(k2_zfmisc_1(C_192, D_191))) | ~v1_funct_1(F_193) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_190, B_194))) | ~v1_funct_1(E_195))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.65/2.41  tff(c_2257, plain, (![C_378, A_381, D_377, A_379, E_380, B_376]: (k1_partfun1(A_379, B_376, C_378, D_377, E_380, A_381)=k5_relat_1(E_380, A_381) | ~v1_funct_1(A_381) | ~m1_subset_1(E_380, k1_zfmisc_1(k2_zfmisc_1(A_379, B_376))) | ~v1_funct_1(E_380) | ~r1_tarski(A_381, k2_zfmisc_1(C_378, D_377)))), inference(resolution, [status(thm)], [c_12, c_904])).
% 6.65/2.41  tff(c_2259, plain, (![C_378, D_377, A_381]: (k1_partfun1(k2_struct_0('#skF_1'), k1_xboole_0, C_378, D_377, '#skF_3', A_381)=k5_relat_1('#skF_3', A_381) | ~v1_funct_1(A_381) | ~v1_funct_1('#skF_3') | ~r1_tarski(A_381, k2_zfmisc_1(C_378, D_377)))), inference(resolution, [status(thm)], [c_1351, c_2257])).
% 6.65/2.41  tff(c_2274, plain, (![C_382, D_383, A_384]: (k1_partfun1(k2_struct_0('#skF_1'), k1_xboole_0, C_382, D_383, '#skF_3', A_384)=k5_relat_1('#skF_3', A_384) | ~v1_funct_1(A_384) | ~r1_tarski(A_384, k2_zfmisc_1(C_382, D_383)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2259])).
% 6.65/2.41  tff(c_2408, plain, (![B_413, A_414, C_415]: (k1_partfun1(k2_struct_0('#skF_1'), k1_xboole_0, B_413, A_414, '#skF_3', k2_funct_1(C_415))=k5_relat_1('#skF_3', k2_funct_1(C_415)) | ~v1_funct_1(k2_funct_1(C_415)) | k2_relset_1(A_414, B_413, C_415)!=B_413 | ~v2_funct_1(C_415) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_414, B_413))) | ~v1_funct_2(C_415, A_414, B_413) | ~v1_funct_1(C_415))), inference(resolution, [status(thm)], [c_1173, c_2274])).
% 6.65/2.41  tff(c_2411, plain, (k1_partfun1(k2_struct_0('#skF_1'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1351, c_2408])).
% 6.65/2.41  tff(c_2425, plain, (k1_partfun1(k2_struct_0('#skF_1'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1353, c_52, c_1352, c_666, c_2411])).
% 6.65/2.41  tff(c_789, plain, (![A_179, B_180, C_181]: (k2_tops_2(A_179, B_180, C_181)=k2_funct_1(C_181) | ~v2_funct_1(C_181) | k2_relset_1(A_179, B_180, C_181)!=B_180 | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(C_181, A_179, B_180) | ~v1_funct_1(C_181))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.65/2.41  tff(c_792, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_789])).
% 6.65/2.41  tff(c_803, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_134, c_52, c_792])).
% 6.65/2.41  tff(c_468, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.65/2.41  tff(c_480, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_468])).
% 6.65/2.41  tff(c_50, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.65/2.41  tff(c_65, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50])).
% 6.65/2.41  tff(c_212, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_88, c_88, c_87, c_87, c_87, c_87, c_88, c_88, c_88, c_87, c_87, c_87, c_65])).
% 6.65/2.41  tff(c_213, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_212])).
% 6.65/2.41  tff(c_495, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_213])).
% 6.65/2.41  tff(c_806, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_803, c_495])).
% 6.65/2.41  tff(c_1343, plain, (k1_partfun1(k2_struct_0('#skF_1'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_1339, c_806])).
% 6.65/2.41  tff(c_2429, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_1343])).
% 6.65/2.41  tff(c_2436, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66, c_2429])).
% 6.65/2.41  tff(c_2440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_52, c_2436])).
% 6.65/2.41  tff(c_2442, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1336])).
% 6.65/2.41  tff(c_2462, plain, (![A_416, C_417, B_418]: (k6_partfun1(A_416)=k5_relat_1(C_417, k2_funct_1(C_417)) | k1_xboole_0=B_418 | ~v2_funct_1(C_417) | k2_relset_1(A_416, B_418, C_417)!=B_418 | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_416, B_418))) | ~v1_funct_2(C_417, A_416, B_418) | ~v1_funct_1(C_417))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.65/2.41  tff(c_2466, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_2462])).
% 6.65/2.41  tff(c_2476, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_134, c_52, c_2466])).
% 6.65/2.41  tff(c_2477, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_2442, c_2476])).
% 6.65/2.41  tff(c_2484, plain, (k6_partfun1(k2_struct_0('#skF_1'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2477, c_66])).
% 6.65/2.41  tff(c_2491, plain, (k6_partfun1(k2_struct_0('#skF_1'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_52, c_2484])).
% 6.65/2.41  tff(c_2495, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2491, c_2477])).
% 6.65/2.41  tff(c_3072, plain, (![C_513, B_511, A_516, E_515, A_514, D_512]: (k1_partfun1(A_514, B_511, C_513, D_512, E_515, A_516)=k5_relat_1(E_515, A_516) | ~v1_funct_1(A_516) | ~m1_subset_1(E_515, k1_zfmisc_1(k2_zfmisc_1(A_514, B_511))) | ~v1_funct_1(E_515) | ~r1_tarski(A_516, k2_zfmisc_1(C_513, D_512)))), inference(resolution, [status(thm)], [c_12, c_904])).
% 6.65/2.41  tff(c_3076, plain, (![C_513, D_512, A_516]: (k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_513, D_512, '#skF_3', A_516)=k5_relat_1('#skF_3', A_516) | ~v1_funct_1(A_516) | ~v1_funct_1('#skF_3') | ~r1_tarski(A_516, k2_zfmisc_1(C_513, D_512)))), inference(resolution, [status(thm)], [c_139, c_3072])).
% 6.65/2.41  tff(c_3089, plain, (![C_517, D_518, A_519]: (k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_517, D_518, '#skF_3', A_519)=k5_relat_1('#skF_3', A_519) | ~v1_funct_1(A_519) | ~r1_tarski(A_519, k2_zfmisc_1(C_517, D_518)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3076])).
% 6.65/2.41  tff(c_3102, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3089, c_806])).
% 6.65/2.41  tff(c_3121, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_666, c_2495, c_3102])).
% 6.65/2.41  tff(c_3131, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1173, c_3121])).
% 6.65/2.41  tff(c_3135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_139, c_52, c_134, c_3131])).
% 6.65/2.41  tff(c_3136, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_212])).
% 6.65/2.41  tff(c_3763, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3759, c_3136])).
% 6.65/2.41  tff(c_4241, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_4236, c_4236, c_3763])).
% 6.65/2.41  tff(c_4628, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4624, c_4241])).
% 6.65/2.41  tff(c_4635, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1(k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_4628])).
% 6.65/2.41  tff(c_4638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_52, c_4263, c_4635])).
% 6.65/2.41  tff(c_4640, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_4233])).
% 6.65/2.41  tff(c_4660, plain, (![B_738, C_739, A_740]: (k6_partfun1(B_738)=k5_relat_1(k2_funct_1(C_739), C_739) | k1_xboole_0=B_738 | ~v2_funct_1(C_739) | k2_relset_1(A_740, B_738, C_739)!=B_738 | ~m1_subset_1(C_739, k1_zfmisc_1(k2_zfmisc_1(A_740, B_738))) | ~v1_funct_2(C_739, A_740, B_738) | ~v1_funct_1(C_739))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.65/2.41  tff(c_4664, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_4660])).
% 6.65/2.41  tff(c_4674, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_134, c_52, c_4664])).
% 6.65/2.41  tff(c_4675, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_4640, c_4674])).
% 6.65/2.41  tff(c_4682, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k6_partfun1(k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4675, c_67])).
% 6.65/2.41  tff(c_4689, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_60, c_52, c_4682])).
% 6.65/2.41  tff(c_4693, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4689, c_4675])).
% 6.65/2.41  tff(c_4694, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4689, c_3763])).
% 6.65/2.41  tff(c_4752, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4096, c_4694])).
% 6.65/2.41  tff(c_4758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_139, c_52, c_134, c_3603, c_4693, c_4752])).
% 6.65/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.41  
% 6.65/2.41  Inference rules
% 6.65/2.41  ----------------------
% 6.65/2.41  #Ref     : 0
% 6.65/2.41  #Sup     : 899
% 6.65/2.41  #Fact    : 0
% 6.65/2.41  #Define  : 0
% 6.65/2.41  #Split   : 8
% 6.65/2.41  #Chain   : 0
% 6.65/2.41  #Close   : 0
% 6.65/2.41  
% 6.65/2.41  Ordering : KBO
% 6.65/2.41  
% 6.65/2.41  Simplification rules
% 6.65/2.41  ----------------------
% 6.65/2.41  #Subsume      : 135
% 6.65/2.41  #Demod        : 1447
% 6.65/2.41  #Tautology    : 454
% 6.65/2.41  #SimpNegUnit  : 2
% 6.65/2.41  #BackRed      : 43
% 6.65/2.41  
% 6.65/2.41  #Partial instantiations: 0
% 6.65/2.41  #Strategies tried      : 1
% 6.65/2.41  
% 6.65/2.41  Timing (in seconds)
% 6.65/2.41  ----------------------
% 6.65/2.41  Preprocessing        : 0.40
% 6.65/2.41  Parsing              : 0.22
% 6.65/2.41  CNF conversion       : 0.03
% 6.65/2.41  Main loop            : 1.17
% 6.65/2.41  Inferencing          : 0.42
% 6.65/2.41  Reduction            : 0.45
% 6.65/2.41  Demodulation         : 0.35
% 6.65/2.41  BG Simplification    : 0.04
% 6.65/2.41  Subsumption          : 0.18
% 6.65/2.41  Abstraction          : 0.07
% 6.65/2.41  MUC search           : 0.00
% 6.65/2.41  Cooper               : 0.00
% 6.65/2.42  Total                : 1.64
% 6.65/2.42  Index Insertion      : 0.00
% 6.65/2.42  Index Deletion       : 0.00
% 6.65/2.42  Index Matching       : 0.00
% 6.65/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
