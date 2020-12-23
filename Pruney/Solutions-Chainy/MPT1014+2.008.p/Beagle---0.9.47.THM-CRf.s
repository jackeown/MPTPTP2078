%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:37 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 169 expanded)
%              Number of leaves         :   32 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 568 expanded)
%              Number of equality atoms :   43 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),B)
                & k2_relset_1(A,A,B) = A )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_71,plain,(
    ! [A_40,B_41,D_42] :
      ( r2_relset_1(A_40,B_41,D_42,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_67,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_78,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_81,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_86,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_81])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_96,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_113,plain,(
    ! [A_49,B_50] :
      ( k1_relset_1(A_49,A_49,B_50) = A_49
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_zfmisc_1(A_49,A_49)))
      | ~ v1_funct_2(B_50,A_49,A_49)
      | ~ v1_funct_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_119,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_125,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_104,c_119])).

tff(c_188,plain,(
    ! [B_70,D_66,C_68,A_67,F_69,E_71] :
      ( k1_partfun1(A_67,B_70,C_68,D_66,E_71,F_69) = k5_relat_1(E_71,F_69)
      | ~ m1_subset_1(F_69,k1_zfmisc_1(k2_zfmisc_1(C_68,D_66)))
      | ~ v1_funct_1(F_69)
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_67,B_70)))
      | ~ v1_funct_1(E_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_192,plain,(
    ! [A_67,B_70,E_71] :
      ( k1_partfun1(A_67,B_70,'#skF_1','#skF_1',E_71,'#skF_3') = k5_relat_1(E_71,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_67,B_70)))
      | ~ v1_funct_1(E_71) ) ),
    inference(resolution,[status(thm)],[c_32,c_188])).

tff(c_212,plain,(
    ! [A_75,B_76,E_77] :
      ( k1_partfun1(A_75,B_76,'#skF_1','#skF_1',E_77,'#skF_3') = k5_relat_1(E_77,'#skF_3')
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_1(E_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192])).

tff(c_215,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_212])).

tff(c_221,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_215])).

tff(c_30,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_131,plain,(
    ! [D_51,C_52,A_53,B_54] :
      ( D_51 = C_52
      | ~ r2_relset_1(A_53,B_54,C_52,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_131])).

tff(c_144,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_135])).

tff(c_162,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_226,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_162])).

tff(c_237,plain,(
    ! [C_78,A_81,B_80,F_82,E_79,D_83] :
      ( m1_subset_1(k1_partfun1(A_81,B_80,C_78,D_83,E_79,F_82),k1_zfmisc_1(k2_zfmisc_1(A_81,D_83)))
      | ~ m1_subset_1(F_82,k1_zfmisc_1(k2_zfmisc_1(C_78,D_83)))
      | ~ v1_funct_1(F_82)
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_1(E_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_268,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_237])).

tff(c_282,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_32,c_268])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_282])).

tff(c_285,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_332,plain,(
    ! [A_99,F_101,B_102,C_100,D_98,E_103] :
      ( k1_partfun1(A_99,B_102,C_100,D_98,E_103,F_101) = k5_relat_1(E_103,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_100,D_98)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_99,B_102)))
      | ~ v1_funct_1(E_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_336,plain,(
    ! [A_99,B_102,E_103] :
      ( k1_partfun1(A_99,B_102,'#skF_1','#skF_1',E_103,'#skF_3') = k5_relat_1(E_103,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_99,B_102)))
      | ~ v1_funct_1(E_103) ) ),
    inference(resolution,[status(thm)],[c_32,c_332])).

tff(c_366,plain,(
    ! [A_107,B_108,E_109] :
      ( k1_partfun1(A_107,B_108,'#skF_1','#skF_1',E_109,'#skF_3') = k5_relat_1(E_109,'#skF_3')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(E_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_336])).

tff(c_369,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_366])).

tff(c_375,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_285,c_369])).

tff(c_22,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( k6_relat_1(k1_relat_1(B_8)) = B_8
      | k5_relat_1(A_6,B_8) != A_6
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [B_8,A_6] :
      ( k6_partfun1(k1_relat_1(B_8)) = B_8
      | k5_relat_1(A_6,B_8) != A_6
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_381,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_43])).

tff(c_386,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_42,c_70,c_36,c_86,c_125,c_125,c_381])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_388,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_26])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.51  
% 2.66/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.52  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.52  
% 2.66/1.52  %Foreground sorts:
% 2.66/1.52  
% 2.66/1.52  
% 2.66/1.52  %Background operators:
% 2.66/1.52  
% 2.66/1.52  
% 2.66/1.52  %Foreground operators:
% 2.66/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.66/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.66/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.66/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.66/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.52  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.66/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.52  
% 2.66/1.53  tff(f_117, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_funct_2)).
% 2.66/1.53  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.66/1.53  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.66/1.53  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.66/1.53  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.53  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.53  tff(f_97, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.79/1.53  tff(f_87, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.79/1.53  tff(f_77, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.79/1.53  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.79/1.53  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 2.79/1.53  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_71, plain, (![A_40, B_41, D_42]: (r2_relset_1(A_40, B_41, D_42, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.53  tff(c_77, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_71])).
% 2.79/1.53  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.79/1.53  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_58, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.53  tff(c_61, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.79/1.53  tff(c_67, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 2.79/1.53  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_64, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_58])).
% 2.79/1.53  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 2.79/1.53  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_78, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.53  tff(c_81, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_78])).
% 2.79/1.53  tff(c_86, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_81])).
% 2.79/1.53  tff(c_34, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_96, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.53  tff(c_104, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_96])).
% 2.79/1.53  tff(c_113, plain, (![A_49, B_50]: (k1_relset_1(A_49, A_49, B_50)=A_49 | ~m1_subset_1(B_50, k1_zfmisc_1(k2_zfmisc_1(A_49, A_49))) | ~v1_funct_2(B_50, A_49, A_49) | ~v1_funct_1(B_50))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.53  tff(c_119, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.79/1.53  tff(c_125, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_104, c_119])).
% 2.79/1.53  tff(c_188, plain, (![B_70, D_66, C_68, A_67, F_69, E_71]: (k1_partfun1(A_67, B_70, C_68, D_66, E_71, F_69)=k5_relat_1(E_71, F_69) | ~m1_subset_1(F_69, k1_zfmisc_1(k2_zfmisc_1(C_68, D_66))) | ~v1_funct_1(F_69) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_67, B_70))) | ~v1_funct_1(E_71))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.79/1.53  tff(c_192, plain, (![A_67, B_70, E_71]: (k1_partfun1(A_67, B_70, '#skF_1', '#skF_1', E_71, '#skF_3')=k5_relat_1(E_71, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_67, B_70))) | ~v1_funct_1(E_71))), inference(resolution, [status(thm)], [c_32, c_188])).
% 2.79/1.53  tff(c_212, plain, (![A_75, B_76, E_77]: (k1_partfun1(A_75, B_76, '#skF_1', '#skF_1', E_77, '#skF_3')=k5_relat_1(E_77, '#skF_3') | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_1(E_77))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192])).
% 2.79/1.53  tff(c_215, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_212])).
% 2.79/1.53  tff(c_221, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_215])).
% 2.79/1.53  tff(c_30, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_131, plain, (![D_51, C_52, A_53, B_54]: (D_51=C_52 | ~r2_relset_1(A_53, B_54, C_52, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.53  tff(c_135, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_30, c_131])).
% 2.79/1.53  tff(c_144, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_135])).
% 2.79/1.53  tff(c_162, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_144])).
% 2.79/1.53  tff(c_226, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_162])).
% 2.79/1.53  tff(c_237, plain, (![C_78, A_81, B_80, F_82, E_79, D_83]: (m1_subset_1(k1_partfun1(A_81, B_80, C_78, D_83, E_79, F_82), k1_zfmisc_1(k2_zfmisc_1(A_81, D_83))) | ~m1_subset_1(F_82, k1_zfmisc_1(k2_zfmisc_1(C_78, D_83))) | ~v1_funct_1(F_82) | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_1(E_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.53  tff(c_268, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_221, c_237])).
% 2.79/1.53  tff(c_282, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_32, c_268])).
% 2.79/1.53  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_282])).
% 2.79/1.53  tff(c_285, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_144])).
% 2.79/1.53  tff(c_332, plain, (![A_99, F_101, B_102, C_100, D_98, E_103]: (k1_partfun1(A_99, B_102, C_100, D_98, E_103, F_101)=k5_relat_1(E_103, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_100, D_98))) | ~v1_funct_1(F_101) | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_99, B_102))) | ~v1_funct_1(E_103))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.79/1.53  tff(c_336, plain, (![A_99, B_102, E_103]: (k1_partfun1(A_99, B_102, '#skF_1', '#skF_1', E_103, '#skF_3')=k5_relat_1(E_103, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_99, B_102))) | ~v1_funct_1(E_103))), inference(resolution, [status(thm)], [c_32, c_332])).
% 2.79/1.53  tff(c_366, plain, (![A_107, B_108, E_109]: (k1_partfun1(A_107, B_108, '#skF_1', '#skF_1', E_109, '#skF_3')=k5_relat_1(E_109, '#skF_3') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(E_109))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_336])).
% 2.79/1.53  tff(c_369, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_366])).
% 2.79/1.53  tff(c_375, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_285, c_369])).
% 2.79/1.53  tff(c_22, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.79/1.53  tff(c_6, plain, (![B_8, A_6]: (k6_relat_1(k1_relat_1(B_8))=B_8 | k5_relat_1(A_6, B_8)!=A_6 | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.79/1.53  tff(c_43, plain, (![B_8, A_6]: (k6_partfun1(k1_relat_1(B_8))=B_8 | k5_relat_1(A_6, B_8)!=A_6 | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6])).
% 2.79/1.53  tff(c_381, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_375, c_43])).
% 2.79/1.53  tff(c_386, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_42, c_70, c_36, c_86, c_125, c_125, c_381])).
% 2.79/1.53  tff(c_26, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.79/1.53  tff(c_388, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_26])).
% 2.79/1.53  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_388])).
% 2.79/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.53  
% 2.79/1.53  Inference rules
% 2.79/1.53  ----------------------
% 2.79/1.53  #Ref     : 0
% 2.79/1.53  #Sup     : 78
% 2.79/1.53  #Fact    : 0
% 2.79/1.53  #Define  : 0
% 2.79/1.53  #Split   : 1
% 2.79/1.53  #Chain   : 0
% 2.79/1.53  #Close   : 0
% 2.79/1.53  
% 2.79/1.53  Ordering : KBO
% 2.79/1.53  
% 2.79/1.53  Simplification rules
% 2.79/1.53  ----------------------
% 2.79/1.53  #Subsume      : 0
% 2.79/1.53  #Demod        : 64
% 2.79/1.53  #Tautology    : 35
% 2.79/1.53  #SimpNegUnit  : 1
% 2.79/1.53  #BackRed      : 9
% 2.79/1.53  
% 2.79/1.53  #Partial instantiations: 0
% 2.79/1.53  #Strategies tried      : 1
% 2.79/1.53  
% 2.79/1.53  Timing (in seconds)
% 2.79/1.53  ----------------------
% 2.79/1.54  Preprocessing        : 0.42
% 2.79/1.54  Parsing              : 0.25
% 2.79/1.54  CNF conversion       : 0.02
% 2.79/1.54  Main loop            : 0.26
% 2.79/1.54  Inferencing          : 0.09
% 2.79/1.54  Reduction            : 0.08
% 2.79/1.54  Demodulation         : 0.06
% 2.79/1.54  BG Simplification    : 0.02
% 2.79/1.54  Subsumption          : 0.04
% 2.79/1.54  Abstraction          : 0.02
% 2.79/1.54  MUC search           : 0.00
% 2.79/1.54  Cooper               : 0.00
% 2.79/1.54  Total                : 0.72
% 2.79/1.54  Index Insertion      : 0.00
% 2.79/1.54  Index Deletion       : 0.00
% 2.79/1.54  Index Matching       : 0.00
% 2.79/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
