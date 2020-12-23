%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:09 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 309 expanded)
%              Number of leaves         :   25 ( 109 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 (1022 expanded)
%              Number of equality atoms :   53 ( 324 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_173,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_177,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_173])).

tff(c_30,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_178,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_30])).

tff(c_40,plain,(
    ! [C_15,A_16,B_17] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_39,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_164,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_168,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_164])).

tff(c_242,plain,(
    ! [B_67,A_68,C_69] :
      ( k1_xboole_0 = B_67
      | k1_relset_1(A_68,B_67,C_69) = A_68
      | ~ v1_funct_2(C_69,A_68,B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_248,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_242])).

tff(c_252,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_168,c_248])).

tff(c_253,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_252])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_14),A_13)))
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_260,plain,(
    ! [A_13] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_13)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_20])).

tff(c_300,plain,(
    ! [A_72] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_72)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_260])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26])).

tff(c_45,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_47,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_52,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_30])).

tff(c_57,plain,(
    ! [A_22,B_23,C_24] :
      ( k1_relset_1(A_22,B_23,C_24) = k1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_113,plain,(
    ! [B_39,A_40,C_41] :
      ( k1_xboole_0 = B_39
      | k1_relset_1(A_40,B_39,C_41) = A_40
      | ~ v1_funct_2(C_41,A_40,B_39)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_61,c_119])).

tff(c_124,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_123])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( v1_funct_2(B_14,k1_relat_1(B_14),A_13)
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_134,plain,(
    ! [A_13] :
      ( v1_funct_2('#skF_4','#skF_1',A_13)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_22])).

tff(c_154,plain,(
    ! [A_42] :
      ( v1_funct_2('#skF_4','#skF_1',A_42)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_134])).

tff(c_157,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_157])).

tff(c_162,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_319,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_300,c_162])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_319])).

tff(c_333,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_334,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_339,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_334])).

tff(c_346,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_32])).

tff(c_455,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_459,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_455])).

tff(c_345,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_1','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_30])).

tff(c_461,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_345])).

tff(c_347,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_351,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_347])).

tff(c_340,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_34])).

tff(c_444,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_448,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_444])).

tff(c_16,plain,(
    ! [B_11,C_12] :
      ( k1_relset_1(k1_xboole_0,B_11,C_12) = k1_xboole_0
      | ~ v1_funct_2(C_12,k1_xboole_0,B_11)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_476,plain,(
    ! [B_103,C_104] :
      ( k1_relset_1('#skF_1',B_103,C_104) = '#skF_1'
      | ~ v1_funct_2(C_104,'#skF_1',B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_103))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_333,c_333,c_333,c_16])).

tff(c_479,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_346,c_476])).

tff(c_482,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_448,c_479])).

tff(c_511,plain,(
    ! [B_108,A_109] :
      ( m1_subset_1(B_108,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_108),A_109)))
      | ~ r1_tarski(k2_relat_1(B_108),A_109)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_531,plain,(
    ! [A_109] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_109)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_109)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_511])).

tff(c_552,plain,(
    ! [A_113] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_113)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_36,c_531])).

tff(c_352,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_355,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_359,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_355])).

tff(c_360,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_345])).

tff(c_365,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_369,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_365])).

tff(c_385,plain,(
    ! [B_87,C_88] :
      ( k1_relset_1('#skF_1',B_87,C_88) = '#skF_1'
      | ~ v1_funct_2(C_88,'#skF_1',B_87)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_333,c_333,c_333,c_16])).

tff(c_388,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_346,c_385])).

tff(c_391,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_369,c_388])).

tff(c_422,plain,(
    ! [A_13] :
      ( v1_funct_2('#skF_4','#skF_1',A_13)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_22])).

tff(c_434,plain,(
    ! [A_91] :
      ( v1_funct_2('#skF_4','#skF_1',A_91)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_36,c_422])).

tff(c_437,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_360,c_434])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_437])).

tff(c_442,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_574,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_552,c_442])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.42  
% 2.53/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.42  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.53/1.42  
% 2.53/1.42  %Foreground sorts:
% 2.53/1.42  
% 2.53/1.42  
% 2.53/1.42  %Background operators:
% 2.53/1.42  
% 2.53/1.42  
% 2.53/1.42  %Foreground operators:
% 2.53/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.53/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.53/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.53/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.42  
% 2.53/1.44  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 2.53/1.44  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.53/1.44  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.53/1.44  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.53/1.44  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.53/1.44  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.53/1.44  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.44  tff(c_173, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.44  tff(c_177, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_173])).
% 2.53/1.44  tff(c_30, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.44  tff(c_178, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_30])).
% 2.53/1.44  tff(c_40, plain, (![C_15, A_16, B_17]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.44  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_40])).
% 2.53/1.44  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.44  tff(c_28, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.44  tff(c_39, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.53/1.44  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.44  tff(c_164, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.44  tff(c_168, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_164])).
% 2.53/1.44  tff(c_242, plain, (![B_67, A_68, C_69]: (k1_xboole_0=B_67 | k1_relset_1(A_68, B_67, C_69)=A_68 | ~v1_funct_2(C_69, A_68, B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.44  tff(c_248, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_242])).
% 2.53/1.44  tff(c_252, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_168, c_248])).
% 2.53/1.44  tff(c_253, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_39, c_252])).
% 2.53/1.44  tff(c_20, plain, (![B_14, A_13]: (m1_subset_1(B_14, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_14), A_13))) | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.44  tff(c_260, plain, (![A_13]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_13))) | ~r1_tarski(k2_relat_1('#skF_4'), A_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_20])).
% 2.53/1.44  tff(c_300, plain, (![A_72]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_72))) | ~r1_tarski(k2_relat_1('#skF_4'), A_72))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_260])).
% 2.53/1.44  tff(c_26, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.44  tff(c_38, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26])).
% 2.53/1.44  tff(c_45, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 2.53/1.44  tff(c_47, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.44  tff(c_51, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.53/1.44  tff(c_52, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_30])).
% 2.53/1.44  tff(c_57, plain, (![A_22, B_23, C_24]: (k1_relset_1(A_22, B_23, C_24)=k1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.44  tff(c_61, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_57])).
% 2.53/1.44  tff(c_113, plain, (![B_39, A_40, C_41]: (k1_xboole_0=B_39 | k1_relset_1(A_40, B_39, C_41)=A_40 | ~v1_funct_2(C_41, A_40, B_39) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.44  tff(c_119, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.53/1.44  tff(c_123, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_61, c_119])).
% 2.53/1.44  tff(c_124, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_39, c_123])).
% 2.53/1.44  tff(c_22, plain, (![B_14, A_13]: (v1_funct_2(B_14, k1_relat_1(B_14), A_13) | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.44  tff(c_134, plain, (![A_13]: (v1_funct_2('#skF_4', '#skF_1', A_13) | ~r1_tarski(k2_relat_1('#skF_4'), A_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_22])).
% 2.53/1.44  tff(c_154, plain, (![A_42]: (v1_funct_2('#skF_4', '#skF_1', A_42) | ~r1_tarski(k2_relat_1('#skF_4'), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_134])).
% 2.53/1.44  tff(c_157, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_154])).
% 2.53/1.44  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_157])).
% 2.53/1.44  tff(c_162, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_38])).
% 2.53/1.44  tff(c_319, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_300, c_162])).
% 2.53/1.44  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_319])).
% 2.53/1.44  tff(c_333, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_28])).
% 2.53/1.44  tff(c_334, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.53/1.44  tff(c_339, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_334])).
% 2.53/1.44  tff(c_346, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_32])).
% 2.53/1.44  tff(c_455, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.44  tff(c_459, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_346, c_455])).
% 2.53/1.44  tff(c_345, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_1', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_30])).
% 2.53/1.44  tff(c_461, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_345])).
% 2.53/1.44  tff(c_347, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.44  tff(c_351, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_346, c_347])).
% 2.53/1.44  tff(c_340, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_34])).
% 2.53/1.44  tff(c_444, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.44  tff(c_448, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_346, c_444])).
% 2.53/1.44  tff(c_16, plain, (![B_11, C_12]: (k1_relset_1(k1_xboole_0, B_11, C_12)=k1_xboole_0 | ~v1_funct_2(C_12, k1_xboole_0, B_11) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_11))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.44  tff(c_476, plain, (![B_103, C_104]: (k1_relset_1('#skF_1', B_103, C_104)='#skF_1' | ~v1_funct_2(C_104, '#skF_1', B_103) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_103))))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_333, c_333, c_333, c_16])).
% 2.53/1.44  tff(c_479, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_346, c_476])).
% 2.53/1.44  tff(c_482, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_340, c_448, c_479])).
% 2.53/1.44  tff(c_511, plain, (![B_108, A_109]: (m1_subset_1(B_108, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_108), A_109))) | ~r1_tarski(k2_relat_1(B_108), A_109) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.44  tff(c_531, plain, (![A_109]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_109))) | ~r1_tarski(k2_relat_1('#skF_4'), A_109) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_482, c_511])).
% 2.53/1.44  tff(c_552, plain, (![A_113]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_113))) | ~r1_tarski(k2_relat_1('#skF_4'), A_113))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_36, c_531])).
% 2.53/1.44  tff(c_352, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 2.53/1.44  tff(c_355, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.44  tff(c_359, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_346, c_355])).
% 2.53/1.44  tff(c_360, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_345])).
% 2.53/1.44  tff(c_365, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.44  tff(c_369, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_346, c_365])).
% 2.53/1.44  tff(c_385, plain, (![B_87, C_88]: (k1_relset_1('#skF_1', B_87, C_88)='#skF_1' | ~v1_funct_2(C_88, '#skF_1', B_87) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_333, c_333, c_333, c_16])).
% 2.53/1.44  tff(c_388, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_346, c_385])).
% 2.53/1.44  tff(c_391, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_340, c_369, c_388])).
% 2.53/1.44  tff(c_422, plain, (![A_13]: (v1_funct_2('#skF_4', '#skF_1', A_13) | ~r1_tarski(k2_relat_1('#skF_4'), A_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_391, c_22])).
% 2.53/1.44  tff(c_434, plain, (![A_91]: (v1_funct_2('#skF_4', '#skF_1', A_91) | ~r1_tarski(k2_relat_1('#skF_4'), A_91))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_36, c_422])).
% 2.53/1.44  tff(c_437, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_360, c_434])).
% 2.53/1.44  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_437])).
% 2.53/1.44  tff(c_442, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_38])).
% 2.53/1.44  tff(c_574, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_552, c_442])).
% 2.53/1.44  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_574])).
% 2.53/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.44  
% 2.53/1.44  Inference rules
% 2.53/1.44  ----------------------
% 2.53/1.44  #Ref     : 0
% 2.53/1.44  #Sup     : 128
% 2.53/1.44  #Fact    : 0
% 2.53/1.44  #Define  : 0
% 2.53/1.44  #Split   : 3
% 2.53/1.44  #Chain   : 0
% 2.53/1.44  #Close   : 0
% 2.53/1.44  
% 2.53/1.44  Ordering : KBO
% 2.53/1.44  
% 2.53/1.44  Simplification rules
% 2.53/1.44  ----------------------
% 2.53/1.44  #Subsume      : 11
% 2.53/1.44  #Demod        : 100
% 2.53/1.44  #Tautology    : 65
% 2.53/1.44  #SimpNegUnit  : 5
% 2.53/1.44  #BackRed      : 13
% 2.53/1.44  
% 2.53/1.44  #Partial instantiations: 0
% 2.53/1.44  #Strategies tried      : 1
% 2.53/1.44  
% 2.53/1.44  Timing (in seconds)
% 2.53/1.44  ----------------------
% 2.53/1.44  Preprocessing        : 0.33
% 2.53/1.44  Parsing              : 0.18
% 2.53/1.44  CNF conversion       : 0.02
% 2.53/1.44  Main loop            : 0.28
% 2.53/1.44  Inferencing          : 0.11
% 2.53/1.44  Reduction            : 0.08
% 2.53/1.44  Demodulation         : 0.06
% 2.53/1.44  BG Simplification    : 0.02
% 2.53/1.44  Subsumption          : 0.04
% 2.53/1.44  Abstraction          : 0.01
% 2.53/1.44  MUC search           : 0.00
% 2.53/1.44  Cooper               : 0.00
% 2.53/1.44  Total                : 0.65
% 2.53/1.44  Index Insertion      : 0.00
% 2.53/1.44  Index Deletion       : 0.00
% 2.53/1.44  Index Matching       : 0.00
% 2.53/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
