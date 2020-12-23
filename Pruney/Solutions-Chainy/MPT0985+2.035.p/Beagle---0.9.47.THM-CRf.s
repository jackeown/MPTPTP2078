%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:31 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :  182 (1225 expanded)
%              Number of leaves         :   36 ( 430 expanded)
%              Depth                    :   16
%              Number of atoms          :  404 (3726 expanded)
%              Number of equality atoms :   57 ( 753 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_69,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_69])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12,plain,(
    ! [A_4] :
      ( v1_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_74,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_77,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_74])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_77])).

tff(c_82,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2547,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_83,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14,plain,(
    ! [A_4] :
      ( v1_relat_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1476,plain,(
    ! [C_159,A_160,B_161] :
      ( v4_relat_1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1484,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1476])).

tff(c_84,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) = k1_xboole_0
      | k2_relat_1(A_32) != k1_xboole_0
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_91,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_84])).

tff(c_102,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_93,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) = k1_xboole_0
      | k1_relat_1(A_33) != k1_xboole_0
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_93])).

tff(c_103,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_100])).

tff(c_16,plain,(
    ! [A_5] :
      ( k2_relat_1(k2_funct_1(A_5)) = k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_115,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_158,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_161,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_158])).

tff(c_163,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_161])).

tff(c_18,plain,(
    ! [A_5] :
      ( k1_relat_1(k2_funct_1(A_5)) = k2_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_174,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_53),k2_relat_1(A_53))))
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [C_11,A_9,B_10] :
      ( v4_relat_1(C_11,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_243,plain,(
    ! [A_55] :
      ( v4_relat_1(A_55,k1_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_174,c_24])).

tff(c_386,plain,(
    ! [A_76] :
      ( v4_relat_1(k2_funct_1(A_76),k2_relat_1(A_76))
      | ~ v1_funct_1(k2_funct_1(A_76))
      | ~ v1_relat_1(k2_funct_1(A_76))
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_243])).

tff(c_395,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_386])).

tff(c_401,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_83,c_395])).

tff(c_402,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_405,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_402])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_405])).

tff(c_411,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_122,plain,(
    ! [A_45] :
      ( k1_relat_1(k2_funct_1(A_45)) = k2_relat_1(A_45)
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [A_22] :
      ( v1_funct_2(A_22,k1_relat_1(A_22),k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_595,plain,(
    ! [A_91] :
      ( v1_funct_2(k2_funct_1(A_91),k2_relat_1(A_91),k2_relat_1(k2_funct_1(A_91)))
      | ~ v1_funct_1(k2_funct_1(A_91))
      | ~ v1_relat_1(k2_funct_1(A_91))
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_36])).

tff(c_604,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_595])).

tff(c_612,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_411,c_83,c_604])).

tff(c_618,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_612])).

tff(c_622,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_618])).

tff(c_741,plain,(
    ! [A_100] :
      ( m1_subset_1(k2_funct_1(A_100),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_100),k2_relat_1(k2_funct_1(A_100)))))
      | ~ v1_funct_1(k2_funct_1(A_100))
      | ~ v1_relat_1(k2_funct_1(A_100))
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_174])).

tff(c_768,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_741])).

tff(c_782,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_411,c_83,c_768])).

tff(c_807,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_782])).

tff(c_821,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_807])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_504,plain,(
    ! [B_82,D_83,A_84,C_85] :
      ( k1_xboole_0 = B_82
      | m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_84,C_85)))
      | ~ r1_tarski(B_82,C_85)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_82)))
      | ~ v1_funct_2(D_83,A_84,B_82)
      | ~ v1_funct_1(D_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1367,plain,(
    ! [B_150,D_151,A_152,A_153] :
      ( k1_relat_1(B_150) = k1_xboole_0
      | m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_152,A_153)))
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_152,k1_relat_1(B_150))))
      | ~ v1_funct_2(D_151,A_152,k1_relat_1(B_150))
      | ~ v1_funct_1(D_151)
      | ~ v4_relat_1(B_150,A_153)
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_6,c_504])).

tff(c_1371,plain,(
    ! [A_153] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_153)))
      | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_153)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_821,c_1367])).

tff(c_1379,plain,(
    ! [A_153] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_153)))
      | ~ v4_relat_1('#skF_3',A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_83,c_622,c_1371])).

tff(c_1386,plain,(
    ! [A_155] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_155)))
      | ~ v4_relat_1('#skF_3',A_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_1379])).

tff(c_104,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_1420,plain,(
    ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1386,c_104])).

tff(c_1450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_1420])).

tff(c_1452,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_20,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1456,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1452,c_20])).

tff(c_1578,plain,(
    ! [A_176,B_177,C_178] :
      ( k2_relset_1(A_176,B_177,C_178) = k2_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1587,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1578])).

tff(c_1591,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1587])).

tff(c_1492,plain,(
    ! [A_167] :
      ( k1_relat_1(k2_funct_1(A_167)) = k2_relat_1(A_167)
      | ~ v2_funct_1(A_167)
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1943,plain,(
    ! [A_210] :
      ( v1_funct_2(k2_funct_1(A_210),k2_relat_1(A_210),k2_relat_1(k2_funct_1(A_210)))
      | ~ v1_funct_1(k2_funct_1(A_210))
      | ~ v1_relat_1(k2_funct_1(A_210))
      | ~ v2_funct_1(A_210)
      | ~ v1_funct_1(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1492,c_36])).

tff(c_1952,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_1943])).

tff(c_1960,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_1456,c_83,c_1952])).

tff(c_1966,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1960])).

tff(c_1970,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_1966])).

tff(c_1543,plain,(
    ! [A_172] :
      ( m1_subset_1(A_172,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_172),k2_relat_1(A_172))))
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2052,plain,(
    ! [A_218] :
      ( m1_subset_1(k2_funct_1(A_218),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_218),k2_relat_1(k2_funct_1(A_218)))))
      | ~ v1_funct_1(k2_funct_1(A_218))
      | ~ v1_relat_1(k2_funct_1(A_218))
      | ~ v2_funct_1(A_218)
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1543])).

tff(c_2079,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_2052])).

tff(c_2093,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_1456,c_83,c_2079])).

tff(c_2117,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2093])).

tff(c_2132,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_2117])).

tff(c_1725,plain,(
    ! [B_187,D_188,A_189,C_190] :
      ( k1_xboole_0 = B_187
      | v1_funct_2(D_188,A_189,C_190)
      | ~ r1_tarski(B_187,C_190)
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_zfmisc_1(A_189,B_187)))
      | ~ v1_funct_2(D_188,A_189,B_187)
      | ~ v1_funct_1(D_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2509,plain,(
    ! [B_244,D_245,A_246,A_247] :
      ( k1_relat_1(B_244) = k1_xboole_0
      | v1_funct_2(D_245,A_246,A_247)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_246,k1_relat_1(B_244))))
      | ~ v1_funct_2(D_245,A_246,k1_relat_1(B_244))
      | ~ v1_funct_1(D_245)
      | ~ v4_relat_1(B_244,A_247)
      | ~ v1_relat_1(B_244) ) ),
    inference(resolution,[status(thm)],[c_6,c_1725])).

tff(c_2513,plain,(
    ! [A_247] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_247)
      | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_247)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2132,c_2509])).

tff(c_2523,plain,(
    ! [A_247] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_247)
      | ~ v4_relat_1('#skF_3',A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_83,c_1970,c_2513])).

tff(c_2529,plain,(
    ! [A_248] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_248)
      | ~ v4_relat_1('#skF_3',A_248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_2523])).

tff(c_1451,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2532,plain,(
    ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_2529,c_1451])).

tff(c_2536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_2532])).

tff(c_2538,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_2690,plain,(
    ! [A_268,B_269,C_270] :
      ( k2_relset_1(A_268,B_269,C_270) = k2_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2699,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2690])).

tff(c_2704,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_54,c_2699])).

tff(c_2537,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_2715,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2537])).

tff(c_2634,plain,(
    ! [A_267] :
      ( m1_subset_1(A_267,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_267),k2_relat_1(A_267))))
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [C_11,B_10,A_9] :
      ( v5_relat_1(C_11,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2843,plain,(
    ! [A_279] :
      ( v5_relat_1(A_279,k2_relat_1(A_279))
      | ~ v1_funct_1(A_279)
      | ~ v1_relat_1(A_279) ) ),
    inference(resolution,[status(thm)],[c_2634,c_22])).

tff(c_3045,plain,(
    ! [A_300] :
      ( v5_relat_1(k2_funct_1(A_300),k1_relat_1(A_300))
      | ~ v1_funct_1(k2_funct_1(A_300))
      | ~ v1_relat_1(k2_funct_1(A_300))
      | ~ v2_funct_1(A_300)
      | ~ v1_funct_1(A_300)
      | ~ v1_relat_1(A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2843])).

tff(c_3048,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2715,c_3045])).

tff(c_3053,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_83,c_3048])).

tff(c_3054,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3053])).

tff(c_3057,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3054])).

tff(c_3061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_3057])).

tff(c_3063,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3053])).

tff(c_2714,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2538])).

tff(c_10,plain,(
    ! [A_3] :
      ( k2_relat_1(A_3) = k1_xboole_0
      | k1_relat_1(A_3) != k1_xboole_0
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2716,plain,(
    ! [A_3] :
      ( k2_relat_1(A_3) = '#skF_2'
      | k1_relat_1(A_3) != '#skF_2'
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2704,c_10])).

tff(c_3070,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3063,c_2716])).

tff(c_3072,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3070])).

tff(c_3075,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3072])).

tff(c_3078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_56,c_2714,c_3075])).

tff(c_3079,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3070])).

tff(c_3080,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3070])).

tff(c_3167,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3080,c_36])).

tff(c_3192,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_83,c_3079,c_3167])).

tff(c_34,plain,(
    ! [A_22] :
      ( m1_subset_1(A_22,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22),k2_relat_1(A_22))))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3161,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3080,c_34])).

tff(c_3188,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_83,c_3079,c_3161])).

tff(c_2561,plain,(
    ! [C_254,A_255,B_256] :
      ( v4_relat_1(C_254,A_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2565,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2561])).

tff(c_2555,plain,(
    ! [B_252,A_253] :
      ( r1_tarski(k1_relat_1(B_252),A_253)
      | ~ v4_relat_1(B_252,A_253)
      | ~ v1_relat_1(B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2558,plain,(
    ! [A_253] :
      ( r1_tarski(k1_xboole_0,A_253)
      | ~ v4_relat_1('#skF_3',A_253)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2537,c_2555])).

tff(c_2566,plain,(
    ! [A_257] :
      ( r1_tarski(k1_xboole_0,A_257)
      | ~ v4_relat_1('#skF_3',A_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2558])).

tff(c_2570,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_2565,c_2566])).

tff(c_2712,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2570])).

tff(c_40,plain,(
    ! [D_26,C_25,B_24] :
      ( m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,C_25)))
      | ~ r1_tarski(B_24,C_25)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24)))
      | ~ v1_funct_2(D_26,k1_xboole_0,B_24)
      | ~ v1_funct_1(D_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2907,plain,(
    ! [D_285,C_286,B_287] :
      ( m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1('#skF_2',C_286)))
      | ~ r1_tarski(B_287,C_286)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_287)))
      | ~ v1_funct_2(D_285,'#skF_2',B_287)
      | ~ v1_funct_1(D_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2704,c_2704,c_40])).

tff(c_2915,plain,(
    ! [D_285] :
      ( m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_285,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_285) ) ),
    inference(resolution,[status(thm)],[c_2712,c_2907])).

tff(c_3258,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3188,c_2915])).

tff(c_3282,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_3192,c_3258])).

tff(c_3284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2547,c_3282])).

tff(c_3285,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_3286,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_3514,plain,(
    ! [C_340,A_341,B_342] :
      ( v1_partfun1(C_340,A_341)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342)))
      | ~ v1_xboole_0(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3521,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3286,c_3514])).

tff(c_3524,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3521])).

tff(c_3596,plain,(
    ! [A_345,B_346,C_347] :
      ( k2_relset_1(A_345,B_346,C_347) = k2_relat_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3605,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3596])).

tff(c_3610,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2538,c_3605])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3625,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_2])).

tff(c_3627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3524,c_3625])).

tff(c_3628,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3521])).

tff(c_3820,plain,(
    ! [C_353,A_354,B_355] :
      ( v1_funct_2(C_353,A_354,B_355)
      | ~ v1_partfun1(C_353,A_354)
      | ~ v1_funct_1(C_353)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3826,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3286,c_3820])).

tff(c_3833,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_3628,c_3826])).

tff(c_3835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3285,c_3833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.43/1.96  
% 5.43/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.43/1.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.43/1.96  
% 5.43/1.96  %Foreground sorts:
% 5.43/1.96  
% 5.43/1.96  
% 5.43/1.96  %Background operators:
% 5.43/1.96  
% 5.43/1.96  
% 5.43/1.96  %Foreground operators:
% 5.43/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.43/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.43/1.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.43/1.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.43/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.43/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.43/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.43/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.43/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.43/1.96  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.43/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.43/1.96  tff('#skF_1', type, '#skF_1': $i).
% 5.43/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.43/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.43/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.43/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.43/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.43/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.43/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.43/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.43/1.96  
% 5.65/1.99  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.65/1.99  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.65/1.99  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.65/1.99  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.65/1.99  tff(f_38, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 5.65/1.99  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.65/1.99  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.65/1.99  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.65/1.99  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.65/1.99  tff(f_116, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 5.65/1.99  tff(f_87, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 5.65/1.99  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.65/1.99  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 5.65/1.99  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.65/1.99  tff(c_69, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.65/1.99  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_69])).
% 5.65/1.99  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.65/1.99  tff(c_12, plain, (![A_4]: (v1_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.65/1.99  tff(c_52, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.65/1.99  tff(c_74, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 5.65/1.99  tff(c_77, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_74])).
% 5.65/1.99  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_77])).
% 5.65/1.99  tff(c_82, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_52])).
% 5.65/1.99  tff(c_2547, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_82])).
% 5.65/1.99  tff(c_83, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 5.65/1.99  tff(c_14, plain, (![A_4]: (v1_relat_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.65/1.99  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.65/1.99  tff(c_1476, plain, (![C_159, A_160, B_161]: (v4_relat_1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.65/1.99  tff(c_1484, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1476])).
% 5.65/1.99  tff(c_84, plain, (![A_32]: (k1_relat_1(A_32)=k1_xboole_0 | k2_relat_1(A_32)!=k1_xboole_0 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.65/1.99  tff(c_91, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_84])).
% 5.65/1.99  tff(c_102, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_91])).
% 5.65/1.99  tff(c_93, plain, (![A_33]: (k2_relat_1(A_33)=k1_xboole_0 | k1_relat_1(A_33)!=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.65/1.99  tff(c_100, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_93])).
% 5.65/1.99  tff(c_103, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_102, c_100])).
% 5.65/1.99  tff(c_16, plain, (![A_5]: (k2_relat_1(k2_funct_1(A_5))=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/1.99  tff(c_111, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.65/1.99  tff(c_115, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_111])).
% 5.65/1.99  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.65/1.99  tff(c_158, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.65/1.99  tff(c_161, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_158])).
% 5.65/1.99  tff(c_163, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_161])).
% 5.65/1.99  tff(c_18, plain, (![A_5]: (k1_relat_1(k2_funct_1(A_5))=k2_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/1.99  tff(c_174, plain, (![A_53]: (m1_subset_1(A_53, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_53), k2_relat_1(A_53)))) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.65/1.99  tff(c_24, plain, (![C_11, A_9, B_10]: (v4_relat_1(C_11, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.65/1.99  tff(c_243, plain, (![A_55]: (v4_relat_1(A_55, k1_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_174, c_24])).
% 5.65/1.99  tff(c_386, plain, (![A_76]: (v4_relat_1(k2_funct_1(A_76), k2_relat_1(A_76)) | ~v1_funct_1(k2_funct_1(A_76)) | ~v1_relat_1(k2_funct_1(A_76)) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_18, c_243])).
% 5.65/1.99  tff(c_395, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_386])).
% 5.65/1.99  tff(c_401, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_83, c_395])).
% 5.65/1.99  tff(c_402, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_401])).
% 5.65/1.99  tff(c_405, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_402])).
% 5.65/1.99  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_405])).
% 5.65/1.99  tff(c_411, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_401])).
% 5.65/1.99  tff(c_122, plain, (![A_45]: (k1_relat_1(k2_funct_1(A_45))=k2_relat_1(A_45) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/1.99  tff(c_36, plain, (![A_22]: (v1_funct_2(A_22, k1_relat_1(A_22), k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.65/1.99  tff(c_595, plain, (![A_91]: (v1_funct_2(k2_funct_1(A_91), k2_relat_1(A_91), k2_relat_1(k2_funct_1(A_91))) | ~v1_funct_1(k2_funct_1(A_91)) | ~v1_relat_1(k2_funct_1(A_91)) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_122, c_36])).
% 5.65/1.99  tff(c_604, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_595])).
% 5.65/1.99  tff(c_612, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_411, c_83, c_604])).
% 5.65/1.99  tff(c_618, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_612])).
% 5.65/1.99  tff(c_622, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_618])).
% 5.65/1.99  tff(c_741, plain, (![A_100]: (m1_subset_1(k2_funct_1(A_100), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_100), k2_relat_1(k2_funct_1(A_100))))) | ~v1_funct_1(k2_funct_1(A_100)) | ~v1_relat_1(k2_funct_1(A_100)) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_18, c_174])).
% 5.65/1.99  tff(c_768, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_741])).
% 5.65/1.99  tff(c_782, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_411, c_83, c_768])).
% 5.65/1.99  tff(c_807, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_782])).
% 5.65/1.99  tff(c_821, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_807])).
% 5.65/1.99  tff(c_6, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/1.99  tff(c_504, plain, (![B_82, D_83, A_84, C_85]: (k1_xboole_0=B_82 | m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_84, C_85))) | ~r1_tarski(B_82, C_85) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_82))) | ~v1_funct_2(D_83, A_84, B_82) | ~v1_funct_1(D_83))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.65/1.99  tff(c_1367, plain, (![B_150, D_151, A_152, A_153]: (k1_relat_1(B_150)=k1_xboole_0 | m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_152, A_153))) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_152, k1_relat_1(B_150)))) | ~v1_funct_2(D_151, A_152, k1_relat_1(B_150)) | ~v1_funct_1(D_151) | ~v4_relat_1(B_150, A_153) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_6, c_504])).
% 5.65/1.99  tff(c_1371, plain, (![A_153]: (k1_relat_1('#skF_3')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_153))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_153) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_821, c_1367])).
% 5.65/1.99  tff(c_1379, plain, (![A_153]: (k1_relat_1('#skF_3')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_153))) | ~v4_relat_1('#skF_3', A_153))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_83, c_622, c_1371])).
% 5.65/1.99  tff(c_1386, plain, (![A_155]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_155))) | ~v4_relat_1('#skF_3', A_155))), inference(negUnitSimplification, [status(thm)], [c_103, c_1379])).
% 5.65/1.99  tff(c_104, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_82])).
% 5.65/1.99  tff(c_1420, plain, (~v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1386, c_104])).
% 5.65/1.99  tff(c_1450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_1420])).
% 5.65/1.99  tff(c_1452, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_82])).
% 5.65/1.99  tff(c_20, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.65/1.99  tff(c_1456, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1452, c_20])).
% 5.65/1.99  tff(c_1578, plain, (![A_176, B_177, C_178]: (k2_relset_1(A_176, B_177, C_178)=k2_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.65/1.99  tff(c_1587, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1578])).
% 5.65/1.99  tff(c_1591, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1587])).
% 5.65/1.99  tff(c_1492, plain, (![A_167]: (k1_relat_1(k2_funct_1(A_167))=k2_relat_1(A_167) | ~v2_funct_1(A_167) | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/1.99  tff(c_1943, plain, (![A_210]: (v1_funct_2(k2_funct_1(A_210), k2_relat_1(A_210), k2_relat_1(k2_funct_1(A_210))) | ~v1_funct_1(k2_funct_1(A_210)) | ~v1_relat_1(k2_funct_1(A_210)) | ~v2_funct_1(A_210) | ~v1_funct_1(A_210) | ~v1_relat_1(A_210))), inference(superposition, [status(thm), theory('equality')], [c_1492, c_36])).
% 5.65/1.99  tff(c_1952, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1591, c_1943])).
% 5.65/1.99  tff(c_1960, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_1456, c_83, c_1952])).
% 5.65/1.99  tff(c_1966, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1960])).
% 5.65/1.99  tff(c_1970, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_1966])).
% 5.65/1.99  tff(c_1543, plain, (![A_172]: (m1_subset_1(A_172, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_172), k2_relat_1(A_172)))) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.65/1.99  tff(c_2052, plain, (![A_218]: (m1_subset_1(k2_funct_1(A_218), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_218), k2_relat_1(k2_funct_1(A_218))))) | ~v1_funct_1(k2_funct_1(A_218)) | ~v1_relat_1(k2_funct_1(A_218)) | ~v2_funct_1(A_218) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1543])).
% 5.65/1.99  tff(c_2079, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1591, c_2052])).
% 5.65/1.99  tff(c_2093, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_1456, c_83, c_2079])).
% 5.65/1.99  tff(c_2117, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_2093])).
% 5.65/1.99  tff(c_2132, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_2117])).
% 5.65/1.99  tff(c_1725, plain, (![B_187, D_188, A_189, C_190]: (k1_xboole_0=B_187 | v1_funct_2(D_188, A_189, C_190) | ~r1_tarski(B_187, C_190) | ~m1_subset_1(D_188, k1_zfmisc_1(k2_zfmisc_1(A_189, B_187))) | ~v1_funct_2(D_188, A_189, B_187) | ~v1_funct_1(D_188))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.65/1.99  tff(c_2509, plain, (![B_244, D_245, A_246, A_247]: (k1_relat_1(B_244)=k1_xboole_0 | v1_funct_2(D_245, A_246, A_247) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_246, k1_relat_1(B_244)))) | ~v1_funct_2(D_245, A_246, k1_relat_1(B_244)) | ~v1_funct_1(D_245) | ~v4_relat_1(B_244, A_247) | ~v1_relat_1(B_244))), inference(resolution, [status(thm)], [c_6, c_1725])).
% 5.65/1.99  tff(c_2513, plain, (![A_247]: (k1_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_247) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_247) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2132, c_2509])).
% 5.65/1.99  tff(c_2523, plain, (![A_247]: (k1_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_247) | ~v4_relat_1('#skF_3', A_247))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_83, c_1970, c_2513])).
% 5.65/1.99  tff(c_2529, plain, (![A_248]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_248) | ~v4_relat_1('#skF_3', A_248))), inference(negUnitSimplification, [status(thm)], [c_103, c_2523])).
% 5.65/1.99  tff(c_1451, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_82])).
% 5.65/1.99  tff(c_2532, plain, (~v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_2529, c_1451])).
% 5.65/1.99  tff(c_2536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1484, c_2532])).
% 5.65/1.99  tff(c_2538, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_91])).
% 5.65/1.99  tff(c_2690, plain, (![A_268, B_269, C_270]: (k2_relset_1(A_268, B_269, C_270)=k2_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.65/1.99  tff(c_2699, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2690])).
% 5.65/1.99  tff(c_2704, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2538, c_54, c_2699])).
% 5.65/1.99  tff(c_2537, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_91])).
% 5.65/1.99  tff(c_2715, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2537])).
% 5.65/1.99  tff(c_2634, plain, (![A_267]: (m1_subset_1(A_267, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_267), k2_relat_1(A_267)))) | ~v1_funct_1(A_267) | ~v1_relat_1(A_267))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.65/1.99  tff(c_22, plain, (![C_11, B_10, A_9]: (v5_relat_1(C_11, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.65/1.99  tff(c_2843, plain, (![A_279]: (v5_relat_1(A_279, k2_relat_1(A_279)) | ~v1_funct_1(A_279) | ~v1_relat_1(A_279))), inference(resolution, [status(thm)], [c_2634, c_22])).
% 5.65/1.99  tff(c_3045, plain, (![A_300]: (v5_relat_1(k2_funct_1(A_300), k1_relat_1(A_300)) | ~v1_funct_1(k2_funct_1(A_300)) | ~v1_relat_1(k2_funct_1(A_300)) | ~v2_funct_1(A_300) | ~v1_funct_1(A_300) | ~v1_relat_1(A_300))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2843])).
% 5.65/1.99  tff(c_3048, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2715, c_3045])).
% 5.65/1.99  tff(c_3053, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_83, c_3048])).
% 5.65/1.99  tff(c_3054, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3053])).
% 5.65/1.99  tff(c_3057, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_3054])).
% 5.65/1.99  tff(c_3061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_3057])).
% 5.65/1.99  tff(c_3063, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3053])).
% 5.65/1.99  tff(c_2714, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2538])).
% 5.65/1.99  tff(c_10, plain, (![A_3]: (k2_relat_1(A_3)=k1_xboole_0 | k1_relat_1(A_3)!=k1_xboole_0 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.65/1.99  tff(c_2716, plain, (![A_3]: (k2_relat_1(A_3)='#skF_2' | k1_relat_1(A_3)!='#skF_2' | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2704, c_10])).
% 5.65/1.99  tff(c_3070, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3063, c_2716])).
% 5.65/1.99  tff(c_3072, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3070])).
% 5.65/1.99  tff(c_3075, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_3072])).
% 5.65/1.99  tff(c_3078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_62, c_56, c_2714, c_3075])).
% 5.65/1.99  tff(c_3079, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_3070])).
% 5.65/1.99  tff(c_3080, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_3070])).
% 5.65/1.99  tff(c_3167, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3080, c_36])).
% 5.65/1.99  tff(c_3192, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_83, c_3079, c_3167])).
% 5.65/1.99  tff(c_34, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22), k2_relat_1(A_22)))) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.65/1.99  tff(c_3161, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3080, c_34])).
% 5.65/1.99  tff(c_3188, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_83, c_3079, c_3161])).
% 5.65/1.99  tff(c_2561, plain, (![C_254, A_255, B_256]: (v4_relat_1(C_254, A_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.65/1.99  tff(c_2565, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_2561])).
% 5.65/1.99  tff(c_2555, plain, (![B_252, A_253]: (r1_tarski(k1_relat_1(B_252), A_253) | ~v4_relat_1(B_252, A_253) | ~v1_relat_1(B_252))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/1.99  tff(c_2558, plain, (![A_253]: (r1_tarski(k1_xboole_0, A_253) | ~v4_relat_1('#skF_3', A_253) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2537, c_2555])).
% 5.65/1.99  tff(c_2566, plain, (![A_257]: (r1_tarski(k1_xboole_0, A_257) | ~v4_relat_1('#skF_3', A_257))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2558])).
% 5.65/1.99  tff(c_2570, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_2565, c_2566])).
% 5.65/1.99  tff(c_2712, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2570])).
% 5.65/1.99  tff(c_40, plain, (![D_26, C_25, B_24]: (m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, C_25))) | ~r1_tarski(B_24, C_25) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))) | ~v1_funct_2(D_26, k1_xboole_0, B_24) | ~v1_funct_1(D_26))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.65/1.99  tff(c_2907, plain, (![D_285, C_286, B_287]: (m1_subset_1(D_285, k1_zfmisc_1(k2_zfmisc_1('#skF_2', C_286))) | ~r1_tarski(B_287, C_286) | ~m1_subset_1(D_285, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_287))) | ~v1_funct_2(D_285, '#skF_2', B_287) | ~v1_funct_1(D_285))), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2704, c_2704, c_40])).
% 5.65/1.99  tff(c_2915, plain, (![D_285]: (m1_subset_1(D_285, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1(D_285, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_285, '#skF_2', '#skF_2') | ~v1_funct_1(D_285))), inference(resolution, [status(thm)], [c_2712, c_2907])).
% 5.65/1.99  tff(c_3258, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3188, c_2915])).
% 5.65/1.99  tff(c_3282, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_3192, c_3258])).
% 5.65/1.99  tff(c_3284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2547, c_3282])).
% 5.65/1.99  tff(c_3285, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_82])).
% 5.65/1.99  tff(c_3286, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_82])).
% 5.65/1.99  tff(c_3514, plain, (![C_340, A_341, B_342]: (v1_partfun1(C_340, A_341) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))) | ~v1_xboole_0(A_341))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.65/1.99  tff(c_3521, plain, (v1_partfun1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_3286, c_3514])).
% 5.65/1.99  tff(c_3524, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3521])).
% 5.65/1.99  tff(c_3596, plain, (![A_345, B_346, C_347]: (k2_relset_1(A_345, B_346, C_347)=k2_relat_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.65/1.99  tff(c_3605, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3596])).
% 5.65/1.99  tff(c_3610, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2538, c_3605])).
% 5.65/1.99  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.65/1.99  tff(c_3625, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3610, c_2])).
% 5.65/1.99  tff(c_3627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3524, c_3625])).
% 5.65/1.99  tff(c_3628, plain, (v1_partfun1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_3521])).
% 5.65/1.99  tff(c_3820, plain, (![C_353, A_354, B_355]: (v1_funct_2(C_353, A_354, B_355) | ~v1_partfun1(C_353, A_354) | ~v1_funct_1(C_353) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.65/1.99  tff(c_3826, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_partfun1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3286, c_3820])).
% 5.65/1.99  tff(c_3833, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_3628, c_3826])).
% 5.65/1.99  tff(c_3835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3285, c_3833])).
% 5.65/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/1.99  
% 5.65/1.99  Inference rules
% 5.65/1.99  ----------------------
% 5.65/1.99  #Ref     : 0
% 5.65/1.99  #Sup     : 865
% 5.65/1.99  #Fact    : 0
% 5.65/1.99  #Define  : 0
% 5.65/1.99  #Split   : 23
% 5.65/1.99  #Chain   : 0
% 5.65/1.99  #Close   : 0
% 5.65/1.99  
% 5.65/1.99  Ordering : KBO
% 5.65/1.99  
% 5.65/1.99  Simplification rules
% 5.65/1.99  ----------------------
% 5.65/1.99  #Subsume      : 155
% 5.65/1.99  #Demod        : 970
% 5.65/1.99  #Tautology    : 284
% 5.65/1.99  #SimpNegUnit  : 26
% 5.65/1.99  #BackRed      : 46
% 5.65/1.99  
% 5.65/1.99  #Partial instantiations: 0
% 5.65/1.99  #Strategies tried      : 1
% 5.65/1.99  
% 5.65/1.99  Timing (in seconds)
% 5.65/1.99  ----------------------
% 5.65/1.99  Preprocessing        : 0.32
% 5.65/1.99  Parsing              : 0.17
% 5.65/1.99  CNF conversion       : 0.02
% 5.65/1.99  Main loop            : 0.93
% 5.65/1.99  Inferencing          : 0.34
% 5.65/1.99  Reduction            : 0.31
% 5.65/1.99  Demodulation         : 0.22
% 5.65/1.99  BG Simplification    : 0.04
% 5.65/1.99  Subsumption          : 0.16
% 5.65/1.99  Abstraction          : 0.04
% 5.65/1.99  MUC search           : 0.00
% 5.65/1.99  Cooper               : 0.00
% 5.65/1.99  Total                : 1.32
% 5.65/1.99  Index Insertion      : 0.00
% 5.65/1.99  Index Deletion       : 0.00
% 5.65/1.99  Index Matching       : 0.00
% 5.65/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
