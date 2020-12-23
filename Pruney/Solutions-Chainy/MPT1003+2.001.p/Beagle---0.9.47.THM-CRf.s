%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:58 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 248 expanded)
%              Number of leaves         :   33 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 566 expanded)
%              Number of equality atoms :   68 ( 306 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_4,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k8_relset_1(A_51,B_52,C_53,D_54) = k10_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_127,plain,(
    ! [D_54] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_54) = k10_relat_1('#skF_3',D_54) ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_62,plain,(
    ! [C_35,A_36,B_37] :
      ( v4_relat_1(C_35,A_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_6])).

tff(c_72,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_69])).

tff(c_77,plain,(
    ! [B_38,A_39] :
      ( k2_relat_1(k7_relat_1(B_38,A_39)) = k9_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_77])).

tff(c_93,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_89])).

tff(c_109,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( k7_relset_1(A_46,B_47,C_48,D_49) = k9_relat_1(C_48,D_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_112,plain,(
    ! [D_49] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_49) = k9_relat_1('#skF_3',D_49) ),
    inference(resolution,[status(thm)],[c_36,c_109])).

tff(c_32,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_113,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_32])).

tff(c_114,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_113])).

tff(c_129,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_114])).

tff(c_141,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_129])).

tff(c_143,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_141])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_41,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_99,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_103,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_99])).

tff(c_152,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_103,c_155])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_41,c_158])).

tff(c_161,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_162,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_167,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_162])).

tff(c_173,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_36])).

tff(c_174,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_174])).

tff(c_266,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k8_relset_1(A_91,B_92,C_93,D_94) = k10_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_269,plain,(
    ! [D_94] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_94) = k10_relat_1('#skF_3',D_94) ),
    inference(resolution,[status(thm)],[c_173,c_266])).

tff(c_194,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_173,c_194])).

tff(c_211,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = B_78
      | ~ v4_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_214,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_211])).

tff(c_217,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_214])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_221,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_2])).

tff(c_225,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_221])).

tff(c_242,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_relset_1(A_84,B_85,C_86,D_87) = k9_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_245,plain,(
    ! [D_87] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_87) = k9_relat_1('#skF_3',D_87) ),
    inference(resolution,[status(thm)],[c_173,c_242])).

tff(c_188,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_167,c_32])).

tff(c_246,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_188])).

tff(c_247,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_246])).

tff(c_270,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_247])).

tff(c_282,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_270])).

tff(c_284,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_282])).

tff(c_168,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_38])).

tff(c_233,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_237,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_233])).

tff(c_28,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_286,plain,(
    ! [B_96,C_97] :
      ( k1_relset_1('#skF_1',B_96,C_97) = '#skF_1'
      | ~ v1_funct_2(C_97,'#skF_1',B_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_96))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_161,c_161,c_161,c_28])).

tff(c_289,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_173,c_286])).

tff(c_292,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_237,c_289])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:02:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.38  
% 2.21/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.21/1.38  
% 2.21/1.38  %Foreground sorts:
% 2.21/1.38  
% 2.21/1.38  
% 2.21/1.38  %Background operators:
% 2.21/1.38  
% 2.21/1.38  
% 2.21/1.38  %Foreground operators:
% 2.21/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.38  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.21/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.21/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.21/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.21/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.38  
% 2.46/1.40  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 2.46/1.40  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.40  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.46/1.40  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.46/1.40  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.46/1.40  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.46/1.40  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.46/1.40  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.46/1.40  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.40  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.46/1.40  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.40  tff(c_42, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.40  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_42])).
% 2.46/1.40  tff(c_4, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.40  tff(c_124, plain, (![A_51, B_52, C_53, D_54]: (k8_relset_1(A_51, B_52, C_53, D_54)=k10_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.46/1.40  tff(c_127, plain, (![D_54]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_54)=k10_relat_1('#skF_3', D_54))), inference(resolution, [status(thm)], [c_36, c_124])).
% 2.46/1.40  tff(c_62, plain, (![C_35, A_36, B_37]: (v4_relat_1(C_35, A_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.40  tff(c_66, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.46/1.40  tff(c_6, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.40  tff(c_69, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_6])).
% 2.46/1.40  tff(c_72, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_69])).
% 2.46/1.40  tff(c_77, plain, (![B_38, A_39]: (k2_relat_1(k7_relat_1(B_38, A_39))=k9_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.40  tff(c_89, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72, c_77])).
% 2.46/1.40  tff(c_93, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_89])).
% 2.46/1.40  tff(c_109, plain, (![A_46, B_47, C_48, D_49]: (k7_relset_1(A_46, B_47, C_48, D_49)=k9_relat_1(C_48, D_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.40  tff(c_112, plain, (![D_49]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_49)=k9_relat_1('#skF_3', D_49))), inference(resolution, [status(thm)], [c_36, c_109])).
% 2.46/1.40  tff(c_32, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.40  tff(c_113, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_32])).
% 2.46/1.40  tff(c_114, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_113])).
% 2.46/1.40  tff(c_129, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_114])).
% 2.46/1.40  tff(c_141, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_129])).
% 2.46/1.40  tff(c_143, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_141])).
% 2.46/1.40  tff(c_34, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.40  tff(c_41, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.46/1.40  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.40  tff(c_99, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.46/1.40  tff(c_103, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_99])).
% 2.46/1.40  tff(c_152, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.40  tff(c_155, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_152])).
% 2.46/1.40  tff(c_158, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_103, c_155])).
% 2.46/1.40  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_41, c_158])).
% 2.46/1.40  tff(c_161, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 2.46/1.40  tff(c_162, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.46/1.40  tff(c_167, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_162])).
% 2.46/1.40  tff(c_173, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_36])).
% 2.46/1.40  tff(c_174, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.40  tff(c_178, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173, c_174])).
% 2.46/1.40  tff(c_266, plain, (![A_91, B_92, C_93, D_94]: (k8_relset_1(A_91, B_92, C_93, D_94)=k10_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.46/1.40  tff(c_269, plain, (![D_94]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_94)=k10_relat_1('#skF_3', D_94))), inference(resolution, [status(thm)], [c_173, c_266])).
% 2.46/1.40  tff(c_194, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.40  tff(c_198, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_173, c_194])).
% 2.46/1.40  tff(c_211, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=B_78 | ~v4_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.40  tff(c_214, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_198, c_211])).
% 2.46/1.40  tff(c_217, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_214])).
% 2.46/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.40  tff(c_221, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_2])).
% 2.46/1.40  tff(c_225, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_221])).
% 2.46/1.40  tff(c_242, plain, (![A_84, B_85, C_86, D_87]: (k7_relset_1(A_84, B_85, C_86, D_87)=k9_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.40  tff(c_245, plain, (![D_87]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_87)=k9_relat_1('#skF_3', D_87))), inference(resolution, [status(thm)], [c_173, c_242])).
% 2.46/1.40  tff(c_188, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_167, c_32])).
% 2.46/1.40  tff(c_246, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_188])).
% 2.46/1.40  tff(c_247, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_246])).
% 2.46/1.40  tff(c_270, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_269, c_247])).
% 2.46/1.40  tff(c_282, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_270])).
% 2.46/1.40  tff(c_284, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_282])).
% 2.46/1.40  tff(c_168, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_38])).
% 2.46/1.40  tff(c_233, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.46/1.40  tff(c_237, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173, c_233])).
% 2.46/1.40  tff(c_28, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.40  tff(c_286, plain, (![B_96, C_97]: (k1_relset_1('#skF_1', B_96, C_97)='#skF_1' | ~v1_funct_2(C_97, '#skF_1', B_96) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_96))))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_161, c_161, c_161, c_28])).
% 2.46/1.40  tff(c_289, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_173, c_286])).
% 2.46/1.40  tff(c_292, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_237, c_289])).
% 2.46/1.40  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_292])).
% 2.46/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.40  
% 2.46/1.40  Inference rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Ref     : 0
% 2.46/1.40  #Sup     : 56
% 2.46/1.40  #Fact    : 0
% 2.46/1.40  #Define  : 0
% 2.46/1.40  #Split   : 1
% 2.46/1.40  #Chain   : 0
% 2.46/1.40  #Close   : 0
% 2.46/1.40  
% 2.46/1.40  Ordering : KBO
% 2.46/1.40  
% 2.46/1.40  Simplification rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Subsume      : 1
% 2.46/1.40  #Demod        : 37
% 2.46/1.40  #Tautology    : 33
% 2.46/1.40  #SimpNegUnit  : 3
% 2.46/1.40  #BackRed      : 5
% 2.46/1.40  
% 2.46/1.40  #Partial instantiations: 0
% 2.46/1.40  #Strategies tried      : 1
% 2.46/1.40  
% 2.46/1.40  Timing (in seconds)
% 2.46/1.40  ----------------------
% 2.46/1.40  Preprocessing        : 0.35
% 2.46/1.40  Parsing              : 0.19
% 2.46/1.40  CNF conversion       : 0.02
% 2.46/1.40  Main loop            : 0.21
% 2.46/1.40  Inferencing          : 0.08
% 2.46/1.40  Reduction            : 0.06
% 2.46/1.40  Demodulation         : 0.05
% 2.46/1.40  BG Simplification    : 0.02
% 2.46/1.40  Subsumption          : 0.03
% 2.46/1.40  Abstraction          : 0.01
% 2.46/1.40  MUC search           : 0.00
% 2.46/1.40  Cooper               : 0.00
% 2.46/1.40  Total                : 0.60
% 2.46/1.40  Index Insertion      : 0.00
% 2.46/1.41  Index Deletion       : 0.00
% 2.46/1.41  Index Matching       : 0.00
% 2.46/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
