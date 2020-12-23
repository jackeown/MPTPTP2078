%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:22 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 284 expanded)
%              Number of leaves         :   41 ( 118 expanded)
%              Depth                    :    9
%              Number of atoms          :  208 ( 818 expanded)
%              Number of equality atoms :   35 (  80 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_134,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_xboole_0(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_146,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_134])).

tff(c_148,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_44,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_74,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_36,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_32,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_59,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_316,plain,(
    ! [D_79,C_80,A_81,B_82] :
      ( D_79 = C_80
      | ~ r2_relset_1(A_81,B_82,C_80,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_324,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_316])).

tff(c_339,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_324])).

tff(c_367,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_990,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_367])).

tff(c_994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_990])).

tff(c_995,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_1746,plain,(
    ! [E_177,B_174,D_176,C_175,A_173] :
      ( k1_xboole_0 = C_175
      | v2_funct_1(D_176)
      | ~ v2_funct_1(k1_partfun1(A_173,B_174,B_174,C_175,D_176,E_177))
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(B_174,C_175)))
      | ~ v1_funct_2(E_177,B_174,C_175)
      | ~ v1_funct_1(E_177)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_2(D_176,A_173,B_174)
      | ~ v1_funct_1(D_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1748,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_1746])).

tff(c_1750,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_60,c_1748])).

tff(c_1751,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1750])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1777,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1751,c_2])).

tff(c_1779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_1777])).

tff(c_1781,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_75,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | B_50 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_75])).

tff(c_1794,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1781,c_78])).

tff(c_1780,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_1787,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1780,c_78])).

tff(c_1803,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1794,c_1787])).

tff(c_1814,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1803,c_74])).

tff(c_1871,plain,(
    ! [A_181] :
      ( v1_xboole_0(k6_partfun1(A_181))
      | ~ v1_xboole_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_59,c_134])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1795,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1781,c_4])).

tff(c_1879,plain,(
    ! [A_182] :
      ( k6_partfun1(A_182) = '#skF_1'
      | ~ v1_xboole_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_1871,c_1795])).

tff(c_1887,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1781,c_1879])).

tff(c_1912,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1887,c_60])).

tff(c_1921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1814,c_1912])).

tff(c_1922,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1935,plain,(
    ! [B_190,A_191] :
      ( v1_relat_1(B_190)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_191))
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1941,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_1935])).

tff(c_1950,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1941])).

tff(c_1954,plain,(
    ! [C_192,B_193,A_194] :
      ( v5_relat_1(C_192,B_193)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1965,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1954])).

tff(c_2136,plain,(
    ! [A_210,B_211,D_212] :
      ( r2_relset_1(A_210,B_211,D_212,D_212)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2146,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_59,c_2136])).

tff(c_2149,plain,(
    ! [A_213,B_214,C_215] :
      ( k2_relset_1(A_213,B_214,C_215) = k2_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2164,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2149])).

tff(c_2195,plain,(
    ! [D_217,C_218,A_219,B_220] :
      ( D_217 = C_218
      | ~ r2_relset_1(A_219,B_220,C_218,D_217)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2203,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_2195])).

tff(c_2218,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2203])).

tff(c_2247,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2218])).

tff(c_2955,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2247])).

tff(c_2959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_2955])).

tff(c_2960,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2218])).

tff(c_4541,plain,(
    ! [A_326,B_327,C_328,D_329] :
      ( k2_relset_1(A_326,B_327,C_328) = B_327
      | ~ r2_relset_1(B_327,B_327,k1_partfun1(B_327,A_326,A_326,B_327,D_329,C_328),k6_partfun1(B_327))
      | ~ m1_subset_1(D_329,k1_zfmisc_1(k2_zfmisc_1(B_327,A_326)))
      | ~ v1_funct_2(D_329,B_327,A_326)
      | ~ v1_funct_1(D_329)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_2(C_328,A_326,B_327)
      | ~ v1_funct_1(C_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4559,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2960,c_4541])).

tff(c_4567,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58,c_56,c_54,c_2146,c_2164,c_4559])).

tff(c_28,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4572,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4567,c_28])).

tff(c_4576,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1950,c_1965,c_4567,c_4572])).

tff(c_4578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1922,c_4576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:03:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.02  
% 5.60/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.03  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.60/2.03  
% 5.60/2.03  %Foreground sorts:
% 5.60/2.03  
% 5.60/2.03  
% 5.60/2.03  %Background operators:
% 5.60/2.03  
% 5.60/2.03  
% 5.60/2.03  %Foreground operators:
% 5.60/2.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.60/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.60/2.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.60/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.60/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.60/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.60/2.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.60/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.60/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.60/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.60/2.03  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.60/2.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.60/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.03  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.60/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.60/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.60/2.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.60/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.60/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.60/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.03  
% 5.60/2.04  tff(f_155, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.60/2.04  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.60/2.04  tff(f_96, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.60/2.04  tff(f_47, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.60/2.04  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.60/2.04  tff(f_74, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.60/2.04  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.60/2.04  tff(f_135, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.60/2.04  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.60/2.04  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.60/2.04  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.60/2.04  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.60/2.04  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.60/2.04  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.60/2.04  tff(f_113, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.60/2.04  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.60/2.04  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_134, plain, (![C_65, A_66, B_67]: (v1_xboole_0(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.60/2.04  tff(c_146, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_134])).
% 5.60/2.04  tff(c_148, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_146])).
% 5.60/2.04  tff(c_44, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_74, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.60/2.04  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_36, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.60/2.04  tff(c_12, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.60/2.04  tff(c_60, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 5.60/2.04  tff(c_32, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.60/2.04  tff(c_26, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.60/2.04  tff(c_59, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26])).
% 5.60/2.04  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.04  tff(c_316, plain, (![D_79, C_80, A_81, B_82]: (D_79=C_80 | ~r2_relset_1(A_81, B_82, C_80, D_79) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.60/2.04  tff(c_324, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_316])).
% 5.60/2.04  tff(c_339, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_324])).
% 5.60/2.04  tff(c_367, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_339])).
% 5.60/2.04  tff(c_990, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_367])).
% 5.60/2.04  tff(c_994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_990])).
% 5.60/2.04  tff(c_995, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_339])).
% 5.60/2.04  tff(c_1746, plain, (![E_177, B_174, D_176, C_175, A_173]: (k1_xboole_0=C_175 | v2_funct_1(D_176) | ~v2_funct_1(k1_partfun1(A_173, B_174, B_174, C_175, D_176, E_177)) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(B_174, C_175))) | ~v1_funct_2(E_177, B_174, C_175) | ~v1_funct_1(E_177) | ~m1_subset_1(D_176, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_2(D_176, A_173, B_174) | ~v1_funct_1(D_176))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.60/2.04  tff(c_1748, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_995, c_1746])).
% 5.60/2.04  tff(c_1750, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_48, c_60, c_1748])).
% 5.60/2.04  tff(c_1751, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_1750])).
% 5.60/2.04  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.60/2.04  tff(c_1777, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1751, c_2])).
% 5.60/2.04  tff(c_1779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_1777])).
% 5.60/2.04  tff(c_1781, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_146])).
% 5.60/2.04  tff(c_75, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | B_50=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.60/2.04  tff(c_78, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_2, c_75])).
% 5.60/2.04  tff(c_1794, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1781, c_78])).
% 5.60/2.04  tff(c_1780, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_146])).
% 5.60/2.04  tff(c_1787, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1780, c_78])).
% 5.60/2.04  tff(c_1803, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1794, c_1787])).
% 5.60/2.04  tff(c_1814, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1803, c_74])).
% 5.60/2.04  tff(c_1871, plain, (![A_181]: (v1_xboole_0(k6_partfun1(A_181)) | ~v1_xboole_0(A_181))), inference(resolution, [status(thm)], [c_59, c_134])).
% 5.60/2.04  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.60/2.04  tff(c_1795, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1781, c_4])).
% 5.60/2.04  tff(c_1879, plain, (![A_182]: (k6_partfun1(A_182)='#skF_1' | ~v1_xboole_0(A_182))), inference(resolution, [status(thm)], [c_1871, c_1795])).
% 5.60/2.04  tff(c_1887, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1781, c_1879])).
% 5.60/2.04  tff(c_1912, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1887, c_60])).
% 5.60/2.04  tff(c_1921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1814, c_1912])).
% 5.60/2.04  tff(c_1922, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.60/2.04  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.60/2.04  tff(c_1935, plain, (![B_190, A_191]: (v1_relat_1(B_190) | ~m1_subset_1(B_190, k1_zfmisc_1(A_191)) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.60/2.04  tff(c_1941, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1935])).
% 5.60/2.04  tff(c_1950, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1941])).
% 5.60/2.04  tff(c_1954, plain, (![C_192, B_193, A_194]: (v5_relat_1(C_192, B_193) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.60/2.04  tff(c_1965, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1954])).
% 5.60/2.04  tff(c_2136, plain, (![A_210, B_211, D_212]: (r2_relset_1(A_210, B_211, D_212, D_212) | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.60/2.04  tff(c_2146, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_59, c_2136])).
% 5.60/2.04  tff(c_2149, plain, (![A_213, B_214, C_215]: (k2_relset_1(A_213, B_214, C_215)=k2_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.60/2.04  tff(c_2164, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2149])).
% 5.60/2.04  tff(c_2195, plain, (![D_217, C_218, A_219, B_220]: (D_217=C_218 | ~r2_relset_1(A_219, B_220, C_218, D_217) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.60/2.04  tff(c_2203, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_2195])).
% 5.60/2.04  tff(c_2218, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2203])).
% 5.60/2.04  tff(c_2247, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2218])).
% 5.60/2.04  tff(c_2955, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2247])).
% 5.60/2.04  tff(c_2959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_2955])).
% 5.60/2.04  tff(c_2960, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2218])).
% 5.60/2.04  tff(c_4541, plain, (![A_326, B_327, C_328, D_329]: (k2_relset_1(A_326, B_327, C_328)=B_327 | ~r2_relset_1(B_327, B_327, k1_partfun1(B_327, A_326, A_326, B_327, D_329, C_328), k6_partfun1(B_327)) | ~m1_subset_1(D_329, k1_zfmisc_1(k2_zfmisc_1(B_327, A_326))) | ~v1_funct_2(D_329, B_327, A_326) | ~v1_funct_1(D_329) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_2(C_328, A_326, B_327) | ~v1_funct_1(C_328))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.60/2.04  tff(c_4559, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2960, c_4541])).
% 5.60/2.04  tff(c_4567, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58, c_56, c_54, c_2146, c_2164, c_4559])).
% 5.60/2.04  tff(c_28, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.60/2.04  tff(c_4572, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4567, c_28])).
% 5.60/2.04  tff(c_4576, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1950, c_1965, c_4567, c_4572])).
% 5.60/2.04  tff(c_4578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1922, c_4576])).
% 5.60/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.04  
% 5.60/2.04  Inference rules
% 5.60/2.04  ----------------------
% 5.60/2.04  #Ref     : 0
% 5.60/2.04  #Sup     : 1206
% 5.60/2.04  #Fact    : 0
% 5.60/2.04  #Define  : 0
% 5.60/2.04  #Split   : 20
% 5.60/2.04  #Chain   : 0
% 5.60/2.04  #Close   : 0
% 5.60/2.04  
% 5.60/2.04  Ordering : KBO
% 5.60/2.04  
% 5.60/2.04  Simplification rules
% 5.60/2.04  ----------------------
% 5.60/2.04  #Subsume      : 271
% 5.60/2.04  #Demod        : 656
% 5.60/2.04  #Tautology    : 255
% 5.60/2.04  #SimpNegUnit  : 4
% 5.60/2.04  #BackRed      : 41
% 5.60/2.04  
% 5.60/2.04  #Partial instantiations: 0
% 5.60/2.04  #Strategies tried      : 1
% 5.60/2.04  
% 5.60/2.04  Timing (in seconds)
% 5.60/2.04  ----------------------
% 5.60/2.05  Preprocessing        : 0.35
% 5.60/2.05  Parsing              : 0.19
% 5.60/2.05  CNF conversion       : 0.02
% 5.60/2.05  Main loop            : 0.93
% 5.60/2.05  Inferencing          : 0.30
% 5.60/2.05  Reduction            : 0.32
% 5.60/2.05  Demodulation         : 0.22
% 5.60/2.05  BG Simplification    : 0.04
% 5.60/2.05  Subsumption          : 0.19
% 5.60/2.05  Abstraction          : 0.04
% 5.60/2.05  MUC search           : 0.00
% 5.60/2.05  Cooper               : 0.00
% 5.60/2.05  Total                : 1.32
% 5.60/2.05  Index Insertion      : 0.00
% 5.60/2.05  Index Deletion       : 0.00
% 5.60/2.05  Index Matching       : 0.00
% 5.60/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
