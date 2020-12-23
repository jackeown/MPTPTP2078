%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 698 expanded)
%              Number of leaves         :   23 ( 217 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 (2454 expanded)
%              Number of equality atoms :   23 ( 658 expanded)
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

tff(f_96,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_73,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_16,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_31,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( r2_relset_1(A_27,B_28,C_29,C_29)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [C_31] :
      ( r2_relset_1('#skF_1','#skF_2',C_31,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_58])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_33,plain,(
    ! [C_21,B_22,A_23] :
      ( v1_xboole_0(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(B_22,A_23)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_43,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_partfun1(C_24,A_25)
      | ~ v1_funct_2(C_24,A_25,B_26)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | v1_xboole_0(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_49,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_43])).

tff(c_56,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_49])).

tff(c_57,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_56])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_52,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_46])).

tff(c_53,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_52])).

tff(c_18,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_72,plain,(
    ! [D_32,C_33,A_34,B_35] :
      ( D_32 = C_33
      | ~ r1_partfun1(C_33,D_32)
      | ~ v1_partfun1(D_32,A_34)
      | ~ v1_partfun1(C_33,A_34)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(D_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_34,B_35] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_34)
      | ~ v1_partfun1('#skF_3',A_34)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_77,plain,(
    ! [A_34,B_35] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_34)
      | ~ v1_partfun1('#skF_3',A_34)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_74])).

tff(c_79,plain,(
    ! [A_36,B_37] :
      ( ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_82,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_57,c_53,c_82])).

tff(c_87,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_14,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_91,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_14])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_91])).

tff(c_102,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_109])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_120,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_115])).

tff(c_130,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_20])).

tff(c_131,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_26])).

tff(c_142,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( r2_relset_1(A_42,B_43,C_44,C_44)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_149,plain,(
    ! [C_46] :
      ( r2_relset_1('#skF_1','#skF_1',C_46,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_131,c_142])).

tff(c_155,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_149])).

tff(c_132,plain,(
    ! [C_39,B_40,A_41] :
      ( v1_xboole_0(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(B_40,A_41)))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_139,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_131,c_132])).

tff(c_141,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_122,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_28])).

tff(c_156,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_partfun1(C_47,A_48)
      | ~ v1_funct_2(C_47,A_48,B_49)
      | ~ v1_funct_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_159,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_131,c_156])).

tff(c_165,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_122,c_159])).

tff(c_166,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_165])).

tff(c_121,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_22])).

tff(c_162,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_130,c_156])).

tff(c_169,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_121,c_162])).

tff(c_170,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_169])).

tff(c_171,plain,(
    ! [D_50,C_51,A_52,B_53] :
      ( D_50 = C_51
      | ~ r1_partfun1(C_51,D_50)
      | ~ v1_partfun1(D_50,A_52)
      | ~ v1_partfun1(C_51,A_52)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(D_50)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_173,plain,(
    ! [A_52,B_53] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_52)
      | ~ v1_partfun1('#skF_3',A_52)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_171])).

tff(c_176,plain,(
    ! [A_52,B_53] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_52)
      | ~ v1_partfun1('#skF_3',A_52)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_173])).

tff(c_178,plain,(
    ! [A_54,B_55] :
      ( ~ v1_partfun1('#skF_4',A_54)
      | ~ v1_partfun1('#skF_3',A_54)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_181,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_131,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_166,c_170,c_181])).

tff(c_186,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_129,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_14])).

tff(c_190,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_129])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_190])).

tff(c_201,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_140,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_130,c_132])).

tff(c_230,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_140])).

tff(c_127,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_2])).

tff(c_234,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_230,c_127])).

tff(c_200,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_205,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_200,c_127])).

tff(c_220,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_129])).

tff(c_270,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_234,c_220])).

tff(c_219,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_131])).

tff(c_271,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_234,c_219])).

tff(c_206,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_relset_1(A_56,B_57,C_58,C_58)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_211,plain,(
    ! [C_58] :
      ( r2_relset_1('#skF_1','#skF_1',C_58,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_131,c_206])).

tff(c_289,plain,(
    ! [C_64] :
      ( r2_relset_1('#skF_4','#skF_4',C_64,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_234,c_234,c_211])).

tff(c_291,plain,(
    r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_271,c_289])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.25  
% 2.36/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.25  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.25  
% 2.36/1.25  %Foreground sorts:
% 2.36/1.25  
% 2.36/1.25  
% 2.36/1.25  %Background operators:
% 2.36/1.25  
% 2.36/1.25  
% 2.36/1.25  %Foreground operators:
% 2.36/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.25  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.36/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.25  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.36/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.25  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.36/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.25  
% 2.36/1.27  tff(f_96, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.36/1.27  tff(f_42, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.36/1.27  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.36/1.27  tff(f_56, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.36/1.27  tff(f_73, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.36/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.36/1.27  tff(c_16, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_31, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 2.36/1.27  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_58, plain, (![A_27, B_28, C_29, D_30]: (r2_relset_1(A_27, B_28, C_29, C_29) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.27  tff(c_65, plain, (![C_31]: (r2_relset_1('#skF_1', '#skF_2', C_31, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_20, c_58])).
% 2.36/1.27  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_65])).
% 2.36/1.27  tff(c_33, plain, (![C_21, B_22, A_23]: (v1_xboole_0(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(B_22, A_23))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.27  tff(c_40, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_33])).
% 2.36/1.27  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.36/1.27  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_43, plain, (![C_24, A_25, B_26]: (v1_partfun1(C_24, A_25) | ~v1_funct_2(C_24, A_25, B_26) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | v1_xboole_0(B_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.27  tff(c_49, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_43])).
% 2.36/1.27  tff(c_56, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_49])).
% 2.36/1.27  tff(c_57, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_56])).
% 2.36/1.27  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_22, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_46, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.36/1.27  tff(c_52, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_46])).
% 2.36/1.27  tff(c_53, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_52])).
% 2.36/1.27  tff(c_18, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_72, plain, (![D_32, C_33, A_34, B_35]: (D_32=C_33 | ~r1_partfun1(C_33, D_32) | ~v1_partfun1(D_32, A_34) | ~v1_partfun1(C_33, A_34) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(D_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.27  tff(c_74, plain, (![A_34, B_35]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_34) | ~v1_partfun1('#skF_3', A_34) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_72])).
% 2.36/1.27  tff(c_77, plain, (![A_34, B_35]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_34) | ~v1_partfun1('#skF_3', A_34) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_74])).
% 2.36/1.27  tff(c_79, plain, (![A_36, B_37]: (~v1_partfun1('#skF_4', A_36) | ~v1_partfun1('#skF_3', A_36) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(splitLeft, [status(thm)], [c_77])).
% 2.36/1.27  tff(c_82, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.36/1.27  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_57, c_53, c_82])).
% 2.36/1.27  tff(c_87, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_77])).
% 2.36/1.27  tff(c_14, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.27  tff(c_91, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_14])).
% 2.36/1.27  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_91])).
% 2.36/1.27  tff(c_102, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.36/1.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.27  tff(c_109, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_102, c_2])).
% 2.36/1.27  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_109])).
% 2.36/1.27  tff(c_114, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 2.36/1.27  tff(c_115, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16])).
% 2.36/1.27  tff(c_120, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_115])).
% 2.36/1.27  tff(c_130, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_20])).
% 2.36/1.27  tff(c_131, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_26])).
% 2.36/1.27  tff(c_142, plain, (![A_42, B_43, C_44, D_45]: (r2_relset_1(A_42, B_43, C_44, C_44) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.27  tff(c_149, plain, (![C_46]: (r2_relset_1('#skF_1', '#skF_1', C_46, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))))), inference(resolution, [status(thm)], [c_131, c_142])).
% 2.36/1.27  tff(c_155, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_130, c_149])).
% 2.36/1.27  tff(c_132, plain, (![C_39, B_40, A_41]: (v1_xboole_0(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(B_40, A_41))) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.27  tff(c_139, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_131, c_132])).
% 2.36/1.27  tff(c_141, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_139])).
% 2.36/1.27  tff(c_122, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_28])).
% 2.36/1.27  tff(c_156, plain, (![C_47, A_48, B_49]: (v1_partfun1(C_47, A_48) | ~v1_funct_2(C_47, A_48, B_49) | ~v1_funct_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.27  tff(c_159, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_131, c_156])).
% 2.36/1.27  tff(c_165, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_122, c_159])).
% 2.36/1.27  tff(c_166, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_141, c_165])).
% 2.36/1.27  tff(c_121, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_22])).
% 2.36/1.27  tff(c_162, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_130, c_156])).
% 2.36/1.27  tff(c_169, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_121, c_162])).
% 2.36/1.27  tff(c_170, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_141, c_169])).
% 2.36/1.27  tff(c_171, plain, (![D_50, C_51, A_52, B_53]: (D_50=C_51 | ~r1_partfun1(C_51, D_50) | ~v1_partfun1(D_50, A_52) | ~v1_partfun1(C_51, A_52) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(D_50) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.27  tff(c_173, plain, (![A_52, B_53]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_52) | ~v1_partfun1('#skF_3', A_52) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_171])).
% 2.36/1.27  tff(c_176, plain, (![A_52, B_53]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_52) | ~v1_partfun1('#skF_3', A_52) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_173])).
% 2.36/1.27  tff(c_178, plain, (![A_54, B_55]: (~v1_partfun1('#skF_4', A_54) | ~v1_partfun1('#skF_3', A_54) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(splitLeft, [status(thm)], [c_176])).
% 2.36/1.27  tff(c_181, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_131, c_178])).
% 2.36/1.27  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_166, c_170, c_181])).
% 2.36/1.27  tff(c_186, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_176])).
% 2.36/1.27  tff(c_129, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_14])).
% 2.36/1.27  tff(c_190, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_129])).
% 2.36/1.27  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_190])).
% 2.36/1.27  tff(c_201, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_139])).
% 2.36/1.27  tff(c_140, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_130, c_132])).
% 2.36/1.27  tff(c_230, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_140])).
% 2.36/1.27  tff(c_127, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_2])).
% 2.36/1.27  tff(c_234, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_230, c_127])).
% 2.36/1.27  tff(c_200, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_139])).
% 2.36/1.27  tff(c_205, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_200, c_127])).
% 2.36/1.27  tff(c_220, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_129])).
% 2.36/1.27  tff(c_270, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_234, c_234, c_220])).
% 2.36/1.27  tff(c_219, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_131])).
% 2.36/1.27  tff(c_271, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_234, c_234, c_219])).
% 2.36/1.27  tff(c_206, plain, (![A_56, B_57, C_58, D_59]: (r2_relset_1(A_56, B_57, C_58, C_58) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.27  tff(c_211, plain, (![C_58]: (r2_relset_1('#skF_1', '#skF_1', C_58, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))))), inference(resolution, [status(thm)], [c_131, c_206])).
% 2.36/1.27  tff(c_289, plain, (![C_64]: (r2_relset_1('#skF_4', '#skF_4', C_64, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_234, c_234, c_234, c_211])).
% 2.36/1.27  tff(c_291, plain, (r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_271, c_289])).
% 2.36/1.27  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_270, c_291])).
% 2.36/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.27  
% 2.36/1.27  Inference rules
% 2.36/1.27  ----------------------
% 2.36/1.27  #Ref     : 0
% 2.36/1.27  #Sup     : 46
% 2.36/1.27  #Fact    : 0
% 2.36/1.27  #Define  : 0
% 2.36/1.27  #Split   : 5
% 2.36/1.27  #Chain   : 0
% 2.36/1.27  #Close   : 0
% 2.36/1.27  
% 2.36/1.27  Ordering : KBO
% 2.36/1.27  
% 2.36/1.27  Simplification rules
% 2.36/1.27  ----------------------
% 2.36/1.27  #Subsume      : 4
% 2.36/1.27  #Demod        : 90
% 2.36/1.27  #Tautology    : 30
% 2.36/1.27  #SimpNegUnit  : 6
% 2.36/1.27  #BackRed      : 31
% 2.36/1.27  
% 2.36/1.27  #Partial instantiations: 0
% 2.36/1.27  #Strategies tried      : 1
% 2.36/1.27  
% 2.36/1.27  Timing (in seconds)
% 2.36/1.27  ----------------------
% 2.36/1.27  Preprocessing        : 0.29
% 2.36/1.27  Parsing              : 0.16
% 2.36/1.28  CNF conversion       : 0.02
% 2.36/1.28  Main loop            : 0.21
% 2.36/1.28  Inferencing          : 0.08
% 2.36/1.28  Reduction            : 0.07
% 2.36/1.28  Demodulation         : 0.05
% 2.36/1.28  BG Simplification    : 0.01
% 2.36/1.28  Subsumption          : 0.03
% 2.36/1.28  Abstraction          : 0.01
% 2.36/1.28  MUC search           : 0.00
% 2.36/1.28  Cooper               : 0.00
% 2.36/1.28  Total                : 0.55
% 2.36/1.28  Index Insertion      : 0.00
% 2.36/1.28  Index Deletion       : 0.00
% 2.36/1.28  Index Matching       : 0.00
% 2.36/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
