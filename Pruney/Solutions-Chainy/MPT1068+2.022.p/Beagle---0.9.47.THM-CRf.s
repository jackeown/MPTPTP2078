%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:43 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 184 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 668 expanded)
%              Number of equality atoms :   46 ( 159 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(c_22,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_52,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_26,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_41,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_18])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_19,C_21,D_22,B_20,E_24] :
      ( k1_funct_1(k5_relat_1(D_22,E_24),C_21) = k1_funct_1(E_24,k1_funct_1(D_22,C_21))
      | k1_xboole_0 = B_20
      | ~ r2_hidden(C_21,A_19)
      | ~ v1_funct_1(E_24)
      | ~ v1_relat_1(E_24)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(D_22,A_19,B_20)
      | ~ v1_funct_1(D_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_112,plain,(
    ! [A_57,B_56,D_59,E_58,C_55] :
      ( k1_funct_1(k5_relat_1(D_59,E_58),C_55) = k1_funct_1(E_58,k1_funct_1(D_59,C_55))
      | B_56 = '#skF_1'
      | ~ r2_hidden(C_55,A_57)
      | ~ v1_funct_1(E_58)
      | ~ v1_relat_1(E_58)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56)))
      | ~ v1_funct_2(D_59,A_57,B_56)
      | ~ v1_funct_1(D_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_14])).

tff(c_120,plain,(
    ! [B_62,D_64,A_63,B_61,E_60] :
      ( k1_funct_1(k5_relat_1(D_64,E_60),A_63) = k1_funct_1(E_60,k1_funct_1(D_64,A_63))
      | B_61 = '#skF_1'
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_62,B_61)))
      | ~ v1_funct_2(D_64,B_62,B_61)
      | ~ v1_funct_1(D_64)
      | v1_xboole_0(B_62)
      | ~ m1_subset_1(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_122,plain,(
    ! [E_60,A_63] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_60),A_63) = k1_funct_1(E_60,k1_funct_1('#skF_5',A_63))
      | '#skF_1' = '#skF_4'
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_63,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_120])).

tff(c_127,plain,(
    ! [E_60,A_63] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_60),A_63) = k1_funct_1(E_60,k1_funct_1('#skF_5',A_63))
      | '#skF_1' = '#skF_4'
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_63,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_122])).

tff(c_132,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_2])).

tff(c_136,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_132,c_40])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_136])).

tff(c_141,plain,(
    ! [E_60,A_63] :
      ( '#skF_1' = '#skF_4'
      | k1_funct_1(k5_relat_1('#skF_5',E_60),A_63) = k1_funct_1(E_60,k1_funct_1('#skF_5',A_63))
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ m1_subset_1(A_63,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_143,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_149,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_4])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_149])).

tff(c_168,plain,(
    ! [E_70,A_71] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_70),A_71) = k1_funct_1(E_70,k1_funct_1('#skF_5',A_71))
      | ~ v1_funct_1(E_70)
      | ~ v1_relat_1(E_70)
      | ~ m1_subset_1(A_71,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_153,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_62,plain,(
    ! [D_44,A_47,C_48,E_46,F_43,B_45] :
      ( k1_partfun1(A_47,B_45,C_48,D_44,E_46,F_43) = k5_relat_1(E_46,F_43)
      | ~ m1_subset_1(F_43,k1_zfmisc_1(k2_zfmisc_1(C_48,D_44)))
      | ~ v1_funct_1(F_43)
      | ~ m1_subset_1(E_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_45)))
      | ~ v1_funct_1(E_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    ! [A_47,B_45,E_46] :
      ( k1_partfun1(A_47,B_45,'#skF_4','#skF_2',E_46,'#skF_6') = k5_relat_1(E_46,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_45)))
      | ~ v1_funct_1(E_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_94,plain,(
    ! [A_52,B_53,E_54] :
      ( k1_partfun1(A_52,B_53,'#skF_4','#skF_2',E_54,'#skF_6') = k5_relat_1(E_54,'#skF_6')
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(E_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_97,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_103,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_97])).

tff(c_20,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10,plain,(
    ! [E_12,D_10,A_7,B_8,C_9] :
      ( k1_partfun1(A_7,B_8,B_8,C_9,D_10,E_12) = k8_funct_2(A_7,B_8,C_9,D_10,E_12)
      | k1_xboole_0 = B_8
      | ~ r1_tarski(k2_relset_1(A_7,B_8,D_10),k1_relset_1(B_8,C_9,E_12))
      | ~ m1_subset_1(E_12,k1_zfmisc_1(k2_zfmisc_1(B_8,C_9)))
      | ~ v1_funct_1(E_12)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(D_10,A_7,B_8)
      | ~ v1_funct_1(D_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_155,plain,(
    ! [B_66,C_67,E_69,D_65,A_68] :
      ( k1_partfun1(A_68,B_66,B_66,C_67,D_65,E_69) = k8_funct_2(A_68,B_66,C_67,D_65,E_69)
      | B_66 = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_68,B_66,D_65),k1_relset_1(B_66,C_67,E_69))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(B_66,C_67)))
      | ~ v1_funct_1(E_69)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_68,B_66)))
      | ~ v1_funct_2(D_65,A_68,B_66)
      | ~ v1_funct_1(D_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_10])).

tff(c_158,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | '#skF_1' = '#skF_4'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_155])).

tff(c_161,plain,
    ( k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_103,c_158])).

tff(c_162,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_161])).

tff(c_16,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_163,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_16])).

tff(c_174,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_163])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60,c_26,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:15:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  
% 2.26/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.26/1.25  
% 2.26/1.25  %Foreground sorts:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Background operators:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Foreground operators:
% 2.26/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.26/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.26/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.25  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.25  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.26/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.25  
% 2.26/1.27  tff(f_110, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.26/1.27  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.26/1.27  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.26/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.26/1.27  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.26/1.27  tff(f_85, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.26/1.27  tff(f_68, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.26/1.27  tff(f_58, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.26/1.27  tff(c_22, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_52, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.27  tff(c_60, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_52])).
% 2.26/1.27  tff(c_26, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_34, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.27  tff(c_35, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.27  tff(c_39, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_35])).
% 2.26/1.27  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_41, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39, c_18])).
% 2.26/1.27  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_30, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.27  tff(c_14, plain, (![A_19, C_21, D_22, B_20, E_24]: (k1_funct_1(k5_relat_1(D_22, E_24), C_21)=k1_funct_1(E_24, k1_funct_1(D_22, C_21)) | k1_xboole_0=B_20 | ~r2_hidden(C_21, A_19) | ~v1_funct_1(E_24) | ~v1_relat_1(E_24) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(D_22, A_19, B_20) | ~v1_funct_1(D_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.26/1.27  tff(c_112, plain, (![A_57, B_56, D_59, E_58, C_55]: (k1_funct_1(k5_relat_1(D_59, E_58), C_55)=k1_funct_1(E_58, k1_funct_1(D_59, C_55)) | B_56='#skF_1' | ~r2_hidden(C_55, A_57) | ~v1_funct_1(E_58) | ~v1_relat_1(E_58) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))) | ~v1_funct_2(D_59, A_57, B_56) | ~v1_funct_1(D_59))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_14])).
% 2.26/1.27  tff(c_120, plain, (![B_62, D_64, A_63, B_61, E_60]: (k1_funct_1(k5_relat_1(D_64, E_60), A_63)=k1_funct_1(E_60, k1_funct_1(D_64, A_63)) | B_61='#skF_1' | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_62, B_61))) | ~v1_funct_2(D_64, B_62, B_61) | ~v1_funct_1(D_64) | v1_xboole_0(B_62) | ~m1_subset_1(A_63, B_62))), inference(resolution, [status(thm)], [c_6, c_112])).
% 2.26/1.27  tff(c_122, plain, (![E_60, A_63]: (k1_funct_1(k5_relat_1('#skF_5', E_60), A_63)=k1_funct_1(E_60, k1_funct_1('#skF_5', A_63)) | '#skF_1'='#skF_4' | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_63, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_120])).
% 2.26/1.27  tff(c_127, plain, (![E_60, A_63]: (k1_funct_1(k5_relat_1('#skF_5', E_60), A_63)=k1_funct_1(E_60, k1_funct_1('#skF_5', A_63)) | '#skF_1'='#skF_4' | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_63, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_122])).
% 2.26/1.27  tff(c_132, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_127])).
% 2.26/1.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.27  tff(c_40, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_2])).
% 2.26/1.27  tff(c_136, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_132, c_40])).
% 2.26/1.27  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_136])).
% 2.26/1.27  tff(c_141, plain, (![E_60, A_63]: ('#skF_1'='#skF_4' | k1_funct_1(k5_relat_1('#skF_5', E_60), A_63)=k1_funct_1(E_60, k1_funct_1('#skF_5', A_63)) | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | ~m1_subset_1(A_63, '#skF_3'))), inference(splitRight, [status(thm)], [c_127])).
% 2.26/1.27  tff(c_143, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_141])).
% 2.26/1.27  tff(c_149, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_4])).
% 2.26/1.27  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_149])).
% 2.26/1.27  tff(c_168, plain, (![E_70, A_71]: (k1_funct_1(k5_relat_1('#skF_5', E_70), A_71)=k1_funct_1(E_70, k1_funct_1('#skF_5', A_71)) | ~v1_funct_1(E_70) | ~v1_relat_1(E_70) | ~m1_subset_1(A_71, '#skF_3'))), inference(splitRight, [status(thm)], [c_141])).
% 2.26/1.27  tff(c_153, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_141])).
% 2.26/1.27  tff(c_62, plain, (![D_44, A_47, C_48, E_46, F_43, B_45]: (k1_partfun1(A_47, B_45, C_48, D_44, E_46, F_43)=k5_relat_1(E_46, F_43) | ~m1_subset_1(F_43, k1_zfmisc_1(k2_zfmisc_1(C_48, D_44))) | ~v1_funct_1(F_43) | ~m1_subset_1(E_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_45))) | ~v1_funct_1(E_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.26/1.27  tff(c_66, plain, (![A_47, B_45, E_46]: (k1_partfun1(A_47, B_45, '#skF_4', '#skF_2', E_46, '#skF_6')=k5_relat_1(E_46, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_45))) | ~v1_funct_1(E_46))), inference(resolution, [status(thm)], [c_24, c_62])).
% 2.26/1.27  tff(c_94, plain, (![A_52, B_53, E_54]: (k1_partfun1(A_52, B_53, '#skF_4', '#skF_2', E_54, '#skF_6')=k5_relat_1(E_54, '#skF_6') | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(E_54))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 2.26/1.27  tff(c_97, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_94])).
% 2.26/1.27  tff(c_103, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_97])).
% 2.26/1.27  tff(c_20, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_10, plain, (![E_12, D_10, A_7, B_8, C_9]: (k1_partfun1(A_7, B_8, B_8, C_9, D_10, E_12)=k8_funct_2(A_7, B_8, C_9, D_10, E_12) | k1_xboole_0=B_8 | ~r1_tarski(k2_relset_1(A_7, B_8, D_10), k1_relset_1(B_8, C_9, E_12)) | ~m1_subset_1(E_12, k1_zfmisc_1(k2_zfmisc_1(B_8, C_9))) | ~v1_funct_1(E_12) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(D_10, A_7, B_8) | ~v1_funct_1(D_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.27  tff(c_155, plain, (![B_66, C_67, E_69, D_65, A_68]: (k1_partfun1(A_68, B_66, B_66, C_67, D_65, E_69)=k8_funct_2(A_68, B_66, C_67, D_65, E_69) | B_66='#skF_1' | ~r1_tarski(k2_relset_1(A_68, B_66, D_65), k1_relset_1(B_66, C_67, E_69)) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(B_66, C_67))) | ~v1_funct_1(E_69) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_68, B_66))) | ~v1_funct_2(D_65, A_68, B_66) | ~v1_funct_1(D_65))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_10])).
% 2.26/1.27  tff(c_158, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | '#skF_1'='#skF_4' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_155])).
% 2.26/1.27  tff(c_161, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_103, c_158])).
% 2.26/1.27  tff(c_162, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_153, c_161])).
% 2.26/1.27  tff(c_16, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.27  tff(c_163, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_16])).
% 2.26/1.27  tff(c_174, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_168, c_163])).
% 2.26/1.27  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_60, c_26, c_174])).
% 2.26/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.27  
% 2.26/1.27  Inference rules
% 2.26/1.27  ----------------------
% 2.26/1.27  #Ref     : 0
% 2.26/1.27  #Sup     : 30
% 2.26/1.27  #Fact    : 0
% 2.26/1.27  #Define  : 0
% 2.26/1.27  #Split   : 3
% 2.26/1.27  #Chain   : 0
% 2.26/1.27  #Close   : 0
% 2.26/1.27  
% 2.26/1.27  Ordering : KBO
% 2.26/1.27  
% 2.26/1.27  Simplification rules
% 2.26/1.27  ----------------------
% 2.26/1.27  #Subsume      : 0
% 2.26/1.27  #Demod        : 29
% 2.26/1.27  #Tautology    : 14
% 2.26/1.27  #SimpNegUnit  : 4
% 2.26/1.27  #BackRed      : 9
% 2.26/1.27  
% 2.26/1.27  #Partial instantiations: 0
% 2.26/1.27  #Strategies tried      : 1
% 2.26/1.27  
% 2.26/1.27  Timing (in seconds)
% 2.26/1.27  ----------------------
% 2.26/1.28  Preprocessing        : 0.32
% 2.26/1.28  Parsing              : 0.17
% 2.26/1.28  CNF conversion       : 0.02
% 2.26/1.28  Main loop            : 0.19
% 2.26/1.28  Inferencing          : 0.07
% 2.26/1.28  Reduction            : 0.06
% 2.26/1.28  Demodulation         : 0.04
% 2.26/1.28  BG Simplification    : 0.01
% 2.26/1.28  Subsumption          : 0.03
% 2.26/1.28  Abstraction          : 0.01
% 2.26/1.28  MUC search           : 0.00
% 2.26/1.28  Cooper               : 0.00
% 2.26/1.28  Total                : 0.54
% 2.26/1.28  Index Insertion      : 0.00
% 2.26/1.28  Index Deletion       : 0.00
% 2.26/1.28  Index Matching       : 0.00
% 2.26/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
