%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:41 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 247 expanded)
%              Number of leaves         :   35 ( 105 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 845 expanded)
%              Number of equality atoms :   47 ( 272 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,B,D) = B
                & k2_relset_1(B,C,E) = C )
             => ( C = k1_xboole_0
                | k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_254,plain,(
    ! [E_83,D_81,F_85,C_86,B_82,A_84] :
      ( k1_partfun1(A_84,B_82,C_86,D_81,E_83,F_85) = k5_relat_1(E_83,F_85)
      | ~ m1_subset_1(F_85,k1_zfmisc_1(k2_zfmisc_1(C_86,D_81)))
      | ~ v1_funct_1(F_85)
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_82)))
      | ~ v1_funct_1(E_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_256,plain,(
    ! [A_84,B_82,E_83] :
      ( k1_partfun1(A_84,B_82,'#skF_2','#skF_3',E_83,'#skF_5') = k5_relat_1(E_83,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_82)))
      | ~ v1_funct_1(E_83) ) ),
    inference(resolution,[status(thm)],[c_36,c_254])).

tff(c_265,plain,(
    ! [A_87,B_88,E_89] :
      ( k1_partfun1(A_87,B_88,'#skF_2','#skF_3',E_89,'#skF_5') = k5_relat_1(E_89,'#skF_5')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_256])).

tff(c_271,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_265])).

tff(c_277,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_271])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_284,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_28])).

tff(c_55,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_55])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_32,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_130,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_relset_1(A_51,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_133,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_130])).

tff(c_138,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_133])).

tff(c_64,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_73,plain,(
    ! [B_44,A_45] :
      ( k7_relat_1(B_44,A_45) = B_44
      | ~ v4_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_79,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_76])).

tff(c_94,plain,(
    ! [B_46,A_47] :
      ( k2_relat_1(k7_relat_1(B_46,A_47)) = k9_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_94])).

tff(c_112,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_106])).

tff(c_141,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_112])).

tff(c_34,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_136,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_140,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_136])).

tff(c_72,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = B_8
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_6])).

tff(c_85,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_82])).

tff(c_103,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_94])).

tff(c_110,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_103])).

tff(c_146,plain,(
    k9_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_110])).

tff(c_307,plain,(
    ! [F_96,C_95,E_98,B_97,A_94,D_93] :
      ( m1_subset_1(k1_partfun1(A_94,B_97,C_95,D_93,E_98,F_96),k1_zfmisc_1(k2_zfmisc_1(A_94,D_93)))
      | ~ m1_subset_1(F_96,k1_zfmisc_1(k2_zfmisc_1(C_95,D_93)))
      | ~ v1_funct_1(F_96)
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_94,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_347,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_307])).

tff(c_367,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_36,c_347])).

tff(c_8,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_597,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_367,c_8])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( v4_relat_1(C_14,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_596,plain,(
    v4_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_367,c_12])).

tff(c_635,plain,
    ( k7_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_596,c_6])).

tff(c_638,plain,(
    k7_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_635])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_752,plain,
    ( k9_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = k2_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_2])).

tff(c_756,plain,(
    k9_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_752])).

tff(c_4,plain,(
    ! [B_4,C_6,A_3] :
      ( k9_relat_1(k5_relat_1(B_4,C_6),A_3) = k9_relat_1(C_6,k9_relat_1(B_4,A_3))
      | ~ v1_relat_1(C_6)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_897,plain,
    ( k9_relat_1('#skF_5',k9_relat_1('#skF_4','#skF_1')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_4])).

tff(c_904,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_141,c_146,c_897])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_594,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_367,c_14])).

tff(c_1263,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_594])).

tff(c_1264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_1263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:26:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.53  
% 3.56/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.54  
% 3.56/1.54  %Foreground sorts:
% 3.56/1.54  
% 3.56/1.54  
% 3.56/1.54  %Background operators:
% 3.56/1.54  
% 3.56/1.54  
% 3.56/1.54  %Foreground operators:
% 3.56/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.56/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.56/1.54  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.56/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.56/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.56/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.56/1.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.56/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.56/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.56/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.56/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.56/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.56/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.54  
% 3.56/1.55  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.56/1.55  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.56/1.55  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.56/1.55  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.56/1.55  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.56/1.55  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.56/1.55  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.56/1.55  tff(f_78, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.56/1.55  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 3.56/1.55  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.55  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.55  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.55  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.55  tff(c_254, plain, (![E_83, D_81, F_85, C_86, B_82, A_84]: (k1_partfun1(A_84, B_82, C_86, D_81, E_83, F_85)=k5_relat_1(E_83, F_85) | ~m1_subset_1(F_85, k1_zfmisc_1(k2_zfmisc_1(C_86, D_81))) | ~v1_funct_1(F_85) | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_82))) | ~v1_funct_1(E_83))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.56/1.55  tff(c_256, plain, (![A_84, B_82, E_83]: (k1_partfun1(A_84, B_82, '#skF_2', '#skF_3', E_83, '#skF_5')=k5_relat_1(E_83, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_82))) | ~v1_funct_1(E_83))), inference(resolution, [status(thm)], [c_36, c_254])).
% 3.56/1.55  tff(c_265, plain, (![A_87, B_88, E_89]: (k1_partfun1(A_87, B_88, '#skF_2', '#skF_3', E_89, '#skF_5')=k5_relat_1(E_89, '#skF_5') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_1(E_89))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_256])).
% 3.56/1.55  tff(c_271, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_265])).
% 3.56/1.55  tff(c_277, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_271])).
% 3.56/1.55  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.55  tff(c_284, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_277, c_28])).
% 3.56/1.55  tff(c_55, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.56/1.55  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_55])).
% 3.56/1.55  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_55])).
% 3.56/1.55  tff(c_32, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.55  tff(c_130, plain, (![A_51, B_52, C_53]: (k2_relset_1(A_51, B_52, C_53)=k2_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.55  tff(c_133, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_130])).
% 3.56/1.55  tff(c_138, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_133])).
% 3.56/1.55  tff(c_64, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.56/1.55  tff(c_71, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_64])).
% 3.56/1.55  tff(c_73, plain, (![B_44, A_45]: (k7_relat_1(B_44, A_45)=B_44 | ~v4_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.56/1.55  tff(c_76, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_71, c_73])).
% 3.56/1.55  tff(c_79, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_76])).
% 3.56/1.55  tff(c_94, plain, (![B_46, A_47]: (k2_relat_1(k7_relat_1(B_46, A_47))=k9_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.55  tff(c_106, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_79, c_94])).
% 3.56/1.55  tff(c_112, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_106])).
% 3.56/1.55  tff(c_141, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_112])).
% 3.56/1.55  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.55  tff(c_136, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_130])).
% 3.56/1.55  tff(c_140, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_136])).
% 3.56/1.55  tff(c_72, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_64])).
% 3.56/1.55  tff(c_6, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=B_8 | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.56/1.55  tff(c_82, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_6])).
% 3.56/1.55  tff(c_85, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_82])).
% 3.56/1.55  tff(c_103, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_85, c_94])).
% 3.56/1.55  tff(c_110, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_103])).
% 3.56/1.55  tff(c_146, plain, (k9_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_110])).
% 3.56/1.55  tff(c_307, plain, (![F_96, C_95, E_98, B_97, A_94, D_93]: (m1_subset_1(k1_partfun1(A_94, B_97, C_95, D_93, E_98, F_96), k1_zfmisc_1(k2_zfmisc_1(A_94, D_93))) | ~m1_subset_1(F_96, k1_zfmisc_1(k2_zfmisc_1(C_95, D_93))) | ~v1_funct_1(F_96) | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_94, B_97))) | ~v1_funct_1(E_98))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.56/1.55  tff(c_347, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_277, c_307])).
% 3.56/1.55  tff(c_367, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_36, c_347])).
% 3.56/1.55  tff(c_8, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.56/1.55  tff(c_597, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_367, c_8])).
% 3.56/1.55  tff(c_12, plain, (![C_14, A_12, B_13]: (v4_relat_1(C_14, A_12) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.56/1.55  tff(c_596, plain, (v4_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_367, c_12])).
% 3.56/1.55  tff(c_635, plain, (k7_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')=k5_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_596, c_6])).
% 3.56/1.55  tff(c_638, plain, (k7_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_635])).
% 3.56/1.55  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.55  tff(c_752, plain, (k9_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')=k2_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_638, c_2])).
% 3.56/1.55  tff(c_756, plain, (k9_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_752])).
% 3.56/1.55  tff(c_4, plain, (![B_4, C_6, A_3]: (k9_relat_1(k5_relat_1(B_4, C_6), A_3)=k9_relat_1(C_6, k9_relat_1(B_4, A_3)) | ~v1_relat_1(C_6) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.56/1.55  tff(c_897, plain, (k9_relat_1('#skF_5', k9_relat_1('#skF_4', '#skF_1'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_756, c_4])).
% 3.56/1.55  tff(c_904, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_141, c_146, c_897])).
% 3.56/1.55  tff(c_14, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.55  tff(c_594, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_367, c_14])).
% 3.56/1.55  tff(c_1263, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_904, c_594])).
% 3.56/1.55  tff(c_1264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_1263])).
% 3.56/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.55  
% 3.56/1.55  Inference rules
% 3.56/1.55  ----------------------
% 3.56/1.55  #Ref     : 0
% 3.56/1.55  #Sup     : 285
% 3.56/1.55  #Fact    : 0
% 3.56/1.55  #Define  : 0
% 3.56/1.55  #Split   : 0
% 3.56/1.55  #Chain   : 0
% 3.56/1.55  #Close   : 0
% 3.56/1.55  
% 3.56/1.55  Ordering : KBO
% 3.56/1.55  
% 3.56/1.55  Simplification rules
% 3.56/1.55  ----------------------
% 3.56/1.55  #Subsume      : 0
% 3.56/1.55  #Demod        : 239
% 3.56/1.55  #Tautology    : 104
% 3.56/1.55  #SimpNegUnit  : 1
% 3.56/1.55  #BackRed      : 11
% 3.56/1.55  
% 3.56/1.55  #Partial instantiations: 0
% 3.56/1.55  #Strategies tried      : 1
% 3.56/1.55  
% 3.56/1.55  Timing (in seconds)
% 3.56/1.55  ----------------------
% 3.56/1.56  Preprocessing        : 0.32
% 3.56/1.56  Parsing              : 0.18
% 3.56/1.56  CNF conversion       : 0.02
% 3.56/1.56  Main loop            : 0.47
% 3.56/1.56  Inferencing          : 0.17
% 3.56/1.56  Reduction            : 0.16
% 3.56/1.56  Demodulation         : 0.12
% 3.56/1.56  BG Simplification    : 0.02
% 3.56/1.56  Subsumption          : 0.08
% 3.56/1.56  Abstraction          : 0.03
% 3.56/1.56  MUC search           : 0.00
% 3.56/1.56  Cooper               : 0.00
% 3.56/1.56  Total                : 0.82
% 3.56/1.56  Index Insertion      : 0.00
% 3.56/1.56  Index Deletion       : 0.00
% 3.56/1.56  Index Matching       : 0.00
% 3.56/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
