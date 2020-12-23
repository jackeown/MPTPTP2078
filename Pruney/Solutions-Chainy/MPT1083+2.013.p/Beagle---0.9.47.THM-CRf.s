%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:18 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 129 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 348 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_54,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_61,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_78,plain,(
    ! [B_51,A_52] :
      ( k1_relat_1(B_51) = A_52
      | ~ v1_partfun1(B_51,A_52)
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_81,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_78])).

tff(c_84,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_81])).

tff(c_85,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_208,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_partfun1(C_79,A_80)
      | ~ v1_funct_2(C_79,A_80,B_81)
      | ~ v1_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | v1_xboole_0(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_214,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_208])).

tff(c_218,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_214])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_85,c_218])).

tff(c_221,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_233,plain,(
    ! [A_82,B_83] :
      ( k10_relat_1(A_82,k1_relat_1(B_83)) = k1_relat_1(k5_relat_1(A_82,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_242,plain,(
    ! [A_82] :
      ( k1_relat_1(k5_relat_1(A_82,'#skF_2')) = k10_relat_1(A_82,'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_233])).

tff(c_247,plain,(
    ! [A_84] :
      ( k1_relat_1(k5_relat_1(A_84,'#skF_2')) = k10_relat_1(A_84,'#skF_1')
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_242])).

tff(c_38,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_259,plain,
    ( k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_38])).

tff(c_265,plain,(
    k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_259])).

tff(c_42,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_308,plain,(
    ! [B_97,A_98] :
      ( m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_97),A_98)))
      | ~ r1_tarski(k2_relat_1(B_97),A_98)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_479,plain,(
    ! [B_121,A_122] :
      ( k1_relset_1(k1_relat_1(B_121),A_122,B_121) = k1_relat_1(B_121)
      | ~ r1_tarski(k2_relat_1(B_121),A_122)
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_308,c_16])).

tff(c_482,plain,(
    ! [B_5,A_4] :
      ( k1_relset_1(k1_relat_1(B_5),A_4,B_5) = k1_relat_1(B_5)
      | ~ v1_funct_1(B_5)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_479])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( k8_relset_1(A_17,B_18,C_19,D_20) = k10_relat_1(C_19,D_20)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_518,plain,(
    ! [B_128,A_129,D_130] :
      ( k8_relset_1(k1_relat_1(B_128),A_129,B_128,D_130) = k10_relat_1(B_128,D_130)
      | ~ r1_tarski(k2_relat_1(B_128),A_129)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_308,c_18])).

tff(c_521,plain,(
    ! [B_5,A_4,D_130] :
      ( k8_relset_1(k1_relat_1(B_5),A_4,B_5,D_130) = k10_relat_1(B_5,D_130)
      | ~ v1_funct_1(B_5)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_518])).

tff(c_32,plain,(
    ! [B_31,A_30] :
      ( m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_31),A_30)))
      | ~ r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_438,plain,(
    ! [A_114,B_115,C_116] :
      ( k8_relset_1(A_114,B_115,C_116,B_115) = k1_relset_1(A_114,B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_539,plain,(
    ! [B_134,A_135] :
      ( k8_relset_1(k1_relat_1(B_134),A_135,B_134,A_135) = k1_relset_1(k1_relat_1(B_134),A_135,B_134)
      | ~ r1_tarski(k2_relat_1(B_134),A_135)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_32,c_438])).

tff(c_543,plain,(
    ! [B_136,A_137] :
      ( k8_relset_1(k1_relat_1(B_136),A_137,B_136,A_137) = k1_relset_1(k1_relat_1(B_136),A_137,B_136)
      | ~ v1_funct_1(B_136)
      | ~ v5_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_6,c_539])).

tff(c_665,plain,(
    ! [B_149,D_150] :
      ( k1_relset_1(k1_relat_1(B_149),D_150,B_149) = k10_relat_1(B_149,D_150)
      | ~ v1_funct_1(B_149)
      | ~ v5_relat_1(B_149,D_150)
      | ~ v1_relat_1(B_149)
      | ~ v1_funct_1(B_149)
      | ~ v5_relat_1(B_149,D_150)
      | ~ v1_relat_1(B_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_543])).

tff(c_710,plain,(
    ! [B_155,A_156] :
      ( k10_relat_1(B_155,A_156) = k1_relat_1(B_155)
      | ~ v1_funct_1(B_155)
      | ~ v5_relat_1(B_155,A_156)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1(B_155)
      | ~ v5_relat_1(B_155,A_156)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1(B_155)
      | ~ v5_relat_1(B_155,A_156)
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_665])).

tff(c_714,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_710])).

tff(c_720,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_714])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.86/1.44  
% 2.86/1.44  %Foreground sorts:
% 2.86/1.44  
% 2.86/1.44  
% 2.86/1.44  %Background operators:
% 2.86/1.44  
% 2.86/1.44  
% 2.86/1.44  %Foreground operators:
% 2.86/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.86/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.86/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.86/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.86/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.86/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.86/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.44  
% 3.13/1.46  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 3.13/1.46  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.13/1.46  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.13/1.46  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.13/1.46  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.13/1.46  tff(f_81, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.13/1.46  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.13/1.46  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.13/1.46  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.13/1.46  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.13/1.46  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.13/1.46  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.13/1.46  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.13/1.46  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_54, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.46  tff(c_57, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_54])).
% 3.13/1.46  tff(c_60, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_57])).
% 3.13/1.46  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_61, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.13/1.46  tff(c_65, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_61])).
% 3.13/1.46  tff(c_78, plain, (![B_51, A_52]: (k1_relat_1(B_51)=A_52 | ~v1_partfun1(B_51, A_52) | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.13/1.46  tff(c_81, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_65, c_78])).
% 3.13/1.46  tff(c_84, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_81])).
% 3.13/1.46  tff(c_85, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_84])).
% 3.13/1.46  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_48, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_208, plain, (![C_79, A_80, B_81]: (v1_partfun1(C_79, A_80) | ~v1_funct_2(C_79, A_80, B_81) | ~v1_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | v1_xboole_0(B_81))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.13/1.46  tff(c_214, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_208])).
% 3.13/1.46  tff(c_218, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_214])).
% 3.13/1.46  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_85, c_218])).
% 3.13/1.46  tff(c_221, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_84])).
% 3.13/1.46  tff(c_233, plain, (![A_82, B_83]: (k10_relat_1(A_82, k1_relat_1(B_83))=k1_relat_1(k5_relat_1(A_82, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.13/1.46  tff(c_242, plain, (![A_82]: (k1_relat_1(k5_relat_1(A_82, '#skF_2'))=k10_relat_1(A_82, '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_221, c_233])).
% 3.13/1.46  tff(c_247, plain, (![A_84]: (k1_relat_1(k5_relat_1(A_84, '#skF_2'))=k10_relat_1(A_84, '#skF_1') | ~v1_relat_1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_242])).
% 3.13/1.46  tff(c_38, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_259, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_247, c_38])).
% 3.13/1.46  tff(c_265, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_259])).
% 3.13/1.46  tff(c_42, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.13/1.46  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.46  tff(c_308, plain, (![B_97, A_98]: (m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_97), A_98))) | ~r1_tarski(k2_relat_1(B_97), A_98) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.13/1.46  tff(c_16, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.13/1.46  tff(c_479, plain, (![B_121, A_122]: (k1_relset_1(k1_relat_1(B_121), A_122, B_121)=k1_relat_1(B_121) | ~r1_tarski(k2_relat_1(B_121), A_122) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_308, c_16])).
% 3.13/1.46  tff(c_482, plain, (![B_5, A_4]: (k1_relset_1(k1_relat_1(B_5), A_4, B_5)=k1_relat_1(B_5) | ~v1_funct_1(B_5) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_479])).
% 3.13/1.46  tff(c_18, plain, (![A_17, B_18, C_19, D_20]: (k8_relset_1(A_17, B_18, C_19, D_20)=k10_relat_1(C_19, D_20) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.13/1.46  tff(c_518, plain, (![B_128, A_129, D_130]: (k8_relset_1(k1_relat_1(B_128), A_129, B_128, D_130)=k10_relat_1(B_128, D_130) | ~r1_tarski(k2_relat_1(B_128), A_129) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_308, c_18])).
% 3.13/1.46  tff(c_521, plain, (![B_5, A_4, D_130]: (k8_relset_1(k1_relat_1(B_5), A_4, B_5, D_130)=k10_relat_1(B_5, D_130) | ~v1_funct_1(B_5) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_518])).
% 3.13/1.46  tff(c_32, plain, (![B_31, A_30]: (m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_31), A_30))) | ~r1_tarski(k2_relat_1(B_31), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.13/1.46  tff(c_438, plain, (![A_114, B_115, C_116]: (k8_relset_1(A_114, B_115, C_116, B_115)=k1_relset_1(A_114, B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.13/1.46  tff(c_539, plain, (![B_134, A_135]: (k8_relset_1(k1_relat_1(B_134), A_135, B_134, A_135)=k1_relset_1(k1_relat_1(B_134), A_135, B_134) | ~r1_tarski(k2_relat_1(B_134), A_135) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_32, c_438])).
% 3.13/1.46  tff(c_543, plain, (![B_136, A_137]: (k8_relset_1(k1_relat_1(B_136), A_137, B_136, A_137)=k1_relset_1(k1_relat_1(B_136), A_137, B_136) | ~v1_funct_1(B_136) | ~v5_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_6, c_539])).
% 3.13/1.46  tff(c_665, plain, (![B_149, D_150]: (k1_relset_1(k1_relat_1(B_149), D_150, B_149)=k10_relat_1(B_149, D_150) | ~v1_funct_1(B_149) | ~v5_relat_1(B_149, D_150) | ~v1_relat_1(B_149) | ~v1_funct_1(B_149) | ~v5_relat_1(B_149, D_150) | ~v1_relat_1(B_149))), inference(superposition, [status(thm), theory('equality')], [c_521, c_543])).
% 3.13/1.46  tff(c_710, plain, (![B_155, A_156]: (k10_relat_1(B_155, A_156)=k1_relat_1(B_155) | ~v1_funct_1(B_155) | ~v5_relat_1(B_155, A_156) | ~v1_relat_1(B_155) | ~v1_funct_1(B_155) | ~v5_relat_1(B_155, A_156) | ~v1_relat_1(B_155) | ~v1_funct_1(B_155) | ~v5_relat_1(B_155, A_156) | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_482, c_665])).
% 3.13/1.46  tff(c_714, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_710])).
% 3.13/1.46  tff(c_720, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_714])).
% 3.13/1.46  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_265, c_720])).
% 3.13/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.46  
% 3.13/1.46  Inference rules
% 3.13/1.46  ----------------------
% 3.13/1.46  #Ref     : 0
% 3.13/1.46  #Sup     : 149
% 3.13/1.46  #Fact    : 0
% 3.13/1.46  #Define  : 0
% 3.13/1.46  #Split   : 2
% 3.13/1.46  #Chain   : 0
% 3.13/1.46  #Close   : 0
% 3.13/1.46  
% 3.13/1.46  Ordering : KBO
% 3.13/1.46  
% 3.13/1.46  Simplification rules
% 3.13/1.46  ----------------------
% 3.13/1.46  #Subsume      : 10
% 3.13/1.46  #Demod        : 103
% 3.13/1.46  #Tautology    : 60
% 3.13/1.46  #SimpNegUnit  : 5
% 3.13/1.46  #BackRed      : 0
% 3.13/1.46  
% 3.13/1.46  #Partial instantiations: 0
% 3.13/1.46  #Strategies tried      : 1
% 3.13/1.46  
% 3.13/1.46  Timing (in seconds)
% 3.13/1.46  ----------------------
% 3.13/1.46  Preprocessing        : 0.34
% 3.13/1.46  Parsing              : 0.18
% 3.13/1.46  CNF conversion       : 0.02
% 3.13/1.46  Main loop            : 0.36
% 3.13/1.46  Inferencing          : 0.14
% 3.13/1.46  Reduction            : 0.11
% 3.13/1.46  Demodulation         : 0.08
% 3.13/1.46  BG Simplification    : 0.02
% 3.13/1.46  Subsumption          : 0.05
% 3.13/1.46  Abstraction          : 0.02
% 3.13/1.46  MUC search           : 0.00
% 3.13/1.46  Cooper               : 0.00
% 3.13/1.46  Total                : 0.73
% 3.13/1.46  Index Insertion      : 0.00
% 3.13/1.46  Index Deletion       : 0.00
% 3.13/1.46  Index Matching       : 0.00
% 3.13/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
