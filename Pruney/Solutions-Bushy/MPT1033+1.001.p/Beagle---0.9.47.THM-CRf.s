%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1033+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:17 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 702 expanded)
%              Number of leaves         :   23 ( 219 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 (2496 expanded)
%              Number of equality atoms :   23 ( 664 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_43,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( r2_relset_1(A_24,B_25,C_26,C_26)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [C_28] :
      ( r2_relset_1('#skF_1','#skF_2',C_28,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_55,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_16,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_31,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_57,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_partfun1(C_29,A_30)
      | ~ v1_funct_2(C_29,A_30,B_31)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_66,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_60])).

tff(c_70,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_12,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_73,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_73])).

tff(c_79,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_63,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_69,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_63])).

tff(c_86,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_69])).

tff(c_78,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_18,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_80,plain,(
    ! [D_32,C_33,A_34,B_35] :
      ( D_32 = C_33
      | ~ r1_partfun1(C_33,D_32)
      | ~ v1_partfun1(D_32,A_34)
      | ~ v1_partfun1(C_33,A_34)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(D_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ! [A_34,B_35] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_34)
      | ~ v1_partfun1('#skF_3',A_34)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_80])).

tff(c_85,plain,(
    ! [A_34,B_35] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_34)
      | ~ v1_partfun1('#skF_3',A_34)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_82])).

tff(c_88,plain,(
    ! [A_36,B_37] :
      ( ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_91,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_86,c_78,c_91])).

tff(c_96,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_14,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_100,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_14])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_100])).

tff(c_110,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_116,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_111])).

tff(c_126,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_127,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_26])).

tff(c_138,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( r2_relset_1(A_42,B_43,C_44,C_44)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,(
    ! [C_46] :
      ( r2_relset_1('#skF_1','#skF_1',C_46,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_127,c_138])).

tff(c_151,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_145])).

tff(c_128,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_xboole_0(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_128])).

tff(c_137,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_117,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_28])).

tff(c_152,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_partfun1(C_47,A_48)
      | ~ v1_funct_2(C_47,A_48,B_49)
      | ~ v1_funct_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_152])).

tff(c_161,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_117,c_155])).

tff(c_162,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_161])).

tff(c_124,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_22])).

tff(c_158,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_126,c_152])).

tff(c_165,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_124,c_158])).

tff(c_166,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_165])).

tff(c_167,plain,(
    ! [D_50,C_51,A_52,B_53] :
      ( D_50 = C_51
      | ~ r1_partfun1(C_51,D_50)
      | ~ v1_partfun1(D_50,A_52)
      | ~ v1_partfun1(C_51,A_52)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(D_50)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_169,plain,(
    ! [A_52,B_53] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_52)
      | ~ v1_partfun1('#skF_3',A_52)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_172,plain,(
    ! [A_52,B_53] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_52)
      | ~ v1_partfun1('#skF_3',A_52)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_169])).

tff(c_174,plain,(
    ! [A_54,B_55] :
      ( ~ v1_partfun1('#skF_4',A_54)
      | ~ v1_partfun1('#skF_3',A_54)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_177,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_127,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_162,c_166,c_177])).

tff(c_182,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_125,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_14])).

tff(c_186,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_125])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_186])).

tff(c_197,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_136,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_126,c_128])).

tff(c_226,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_136])).

tff(c_122,plain,(
    ! [A_18] :
      ( A_18 = '#skF_1'
      | ~ v1_xboole_0(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_230,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_226,c_122])).

tff(c_196,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_201,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_196,c_122])).

tff(c_216,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_125])).

tff(c_266,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_230,c_230,c_216])).

tff(c_215,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_127])).

tff(c_267,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_230,c_230,c_215])).

tff(c_202,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_relset_1(A_56,B_57,C_58,C_58)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_207,plain,(
    ! [C_58] :
      ( r2_relset_1('#skF_1','#skF_1',C_58,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_127,c_202])).

tff(c_285,plain,(
    ! [C_64] :
      ( r2_relset_1('#skF_4','#skF_4',C_64,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_230,c_230,c_230,c_207])).

tff(c_287,plain,(
    r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_267,c_285])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_287])).

%------------------------------------------------------------------------------
