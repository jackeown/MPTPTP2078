%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:44 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 117 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 337 expanded)
%              Number of equality atoms :   51 ( 126 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_119,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_104,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_107,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_112,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_107])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_86,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_151,plain,(
    ! [B_66,A_67,C_68] :
      ( k1_xboole_0 = B_66
      | k1_relset_1(A_67,B_66,C_68) = A_67
      | ~ v1_funct_2(C_68,A_67,B_66)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_154,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_151])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_93,c_154])).

tff(c_161,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_160])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_110,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_114,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_110])).

tff(c_125,plain,(
    ! [B_57,A_58] :
      ( k2_relat_1(k5_relat_1(B_57,A_58)) = k2_relat_1(A_58)
      | ~ r1_tarski(k1_relat_1(A_58),k2_relat_1(B_57))
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [A_58] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_58)) = k2_relat_1(A_58)
      | ~ r1_tarski(k1_relat_1(A_58),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_125])).

tff(c_133,plain,(
    ! [A_58] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_58)) = k2_relat_1(A_58)
      | ~ r1_tarski(k1_relat_1(A_58),'#skF_2')
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_128])).

tff(c_172,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_133])).

tff(c_181,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_6,c_112,c_172])).

tff(c_210,plain,(
    ! [A_74,F_70,D_73,B_72,C_69,E_71] :
      ( k4_relset_1(A_74,B_72,C_69,D_73,E_71,F_70) = k5_relat_1(E_71,F_70)
      | ~ m1_subset_1(F_70,k1_zfmisc_1(k2_zfmisc_1(C_69,D_73)))
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_74,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_229,plain,(
    ! [A_75,B_76,E_77] :
      ( k4_relset_1(A_75,B_76,'#skF_2','#skF_3',E_77,'#skF_5') = k5_relat_1(E_77,'#skF_5')
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_44,c_210])).

tff(c_237,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_229])).

tff(c_14,plain,(
    ! [F_16,D_14,E_15,B_12,A_11,C_13] :
      ( m1_subset_1(k4_relset_1(A_11,B_12,C_13,D_14,E_15,F_16),k1_zfmisc_1(k2_zfmisc_1(A_11,D_14)))
      | ~ m1_subset_1(F_16,k1_zfmisc_1(k2_zfmisc_1(C_13,D_14)))
      | ~ m1_subset_1(E_15,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_330,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_14])).

tff(c_334,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_330])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] :
      ( k2_relset_1(A_20,B_21,C_22) = k2_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_349,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_334,c_18])).

tff(c_365,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_349])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_382,plain,(
    ! [A_88,E_84,F_86,D_89,B_85,C_87] :
      ( k1_partfun1(A_88,B_85,C_87,D_89,E_84,F_86) = k5_relat_1(E_84,F_86)
      | ~ m1_subset_1(F_86,k1_zfmisc_1(k2_zfmisc_1(C_87,D_89)))
      | ~ v1_funct_1(F_86)
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_88,B_85)))
      | ~ v1_funct_1(E_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_390,plain,(
    ! [A_88,B_85,E_84] :
      ( k1_partfun1(A_88,B_85,'#skF_2','#skF_3',E_84,'#skF_5') = k5_relat_1(E_84,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_88,B_85)))
      | ~ v1_funct_1(E_84) ) ),
    inference(resolution,[status(thm)],[c_44,c_382])).

tff(c_716,plain,(
    ! [A_98,B_99,E_100] :
      ( k1_partfun1(A_98,B_99,'#skF_2','#skF_3',E_100,'#skF_5') = k5_relat_1(E_100,'#skF_5')
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_1(E_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_390])).

tff(c_743,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_716])).

tff(c_756,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_743])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_761,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_36])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/2.08  
% 3.98/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/2.09  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.98/2.09  
% 3.98/2.09  %Foreground sorts:
% 3.98/2.09  
% 3.98/2.09  
% 3.98/2.09  %Background operators:
% 3.98/2.09  
% 3.98/2.09  
% 3.98/2.09  %Foreground operators:
% 3.98/2.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.98/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.98/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/2.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.98/2.09  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.98/2.09  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/2.09  tff('#skF_5', type, '#skF_5': $i).
% 3.98/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.98/2.09  tff('#skF_2', type, '#skF_2': $i).
% 3.98/2.09  tff('#skF_3', type, '#skF_3': $i).
% 3.98/2.09  tff('#skF_1', type, '#skF_1': $i).
% 3.98/2.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.98/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/2.09  tff('#skF_4', type, '#skF_4': $i).
% 3.98/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/2.09  
% 4.17/2.11  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.17/2.11  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 4.17/2.11  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.17/2.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.17/2.11  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.17/2.11  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.17/2.11  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.17/2.11  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 4.17/2.11  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.17/2.11  tff(f_55, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 4.17/2.11  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.17/2.11  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.17/2.11  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_66, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.17/2.11  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_66])).
% 4.17/2.11  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 4.17/2.11  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.17/2.11  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_104, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/2.11  tff(c_107, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_104])).
% 4.17/2.11  tff(c_112, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_107])).
% 4.17/2.11  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_86, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.17/2.11  tff(c_93, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_86])).
% 4.17/2.11  tff(c_151, plain, (![B_66, A_67, C_68]: (k1_xboole_0=B_66 | k1_relset_1(A_67, B_66, C_68)=A_67 | ~v1_funct_2(C_68, A_67, B_66) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/2.11  tff(c_154, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_151])).
% 4.17/2.11  tff(c_160, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_93, c_154])).
% 4.17/2.11  tff(c_161, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_160])).
% 4.17/2.11  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_72, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_66])).
% 4.17/2.11  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 4.17/2.11  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_110, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_104])).
% 4.17/2.11  tff(c_114, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_110])).
% 4.17/2.11  tff(c_125, plain, (![B_57, A_58]: (k2_relat_1(k5_relat_1(B_57, A_58))=k2_relat_1(A_58) | ~r1_tarski(k1_relat_1(A_58), k2_relat_1(B_57)) | ~v1_relat_1(B_57) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.17/2.11  tff(c_128, plain, (![A_58]: (k2_relat_1(k5_relat_1('#skF_4', A_58))=k2_relat_1(A_58) | ~r1_tarski(k1_relat_1(A_58), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_114, c_125])).
% 4.17/2.11  tff(c_133, plain, (![A_58]: (k2_relat_1(k5_relat_1('#skF_4', A_58))=k2_relat_1(A_58) | ~r1_tarski(k1_relat_1(A_58), '#skF_2') | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_128])).
% 4.17/2.11  tff(c_172, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_161, c_133])).
% 4.17/2.11  tff(c_181, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_6, c_112, c_172])).
% 4.17/2.11  tff(c_210, plain, (![A_74, F_70, D_73, B_72, C_69, E_71]: (k4_relset_1(A_74, B_72, C_69, D_73, E_71, F_70)=k5_relat_1(E_71, F_70) | ~m1_subset_1(F_70, k1_zfmisc_1(k2_zfmisc_1(C_69, D_73))) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_74, B_72))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.17/2.11  tff(c_229, plain, (![A_75, B_76, E_77]: (k4_relset_1(A_75, B_76, '#skF_2', '#skF_3', E_77, '#skF_5')=k5_relat_1(E_77, '#skF_5') | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_44, c_210])).
% 4.17/2.11  tff(c_237, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_229])).
% 4.17/2.11  tff(c_14, plain, (![F_16, D_14, E_15, B_12, A_11, C_13]: (m1_subset_1(k4_relset_1(A_11, B_12, C_13, D_14, E_15, F_16), k1_zfmisc_1(k2_zfmisc_1(A_11, D_14))) | ~m1_subset_1(F_16, k1_zfmisc_1(k2_zfmisc_1(C_13, D_14))) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.17/2.11  tff(c_330, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_237, c_14])).
% 4.17/2.11  tff(c_334, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_330])).
% 4.17/2.11  tff(c_18, plain, (![A_20, B_21, C_22]: (k2_relset_1(A_20, B_21, C_22)=k2_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/2.11  tff(c_349, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_334, c_18])).
% 4.17/2.11  tff(c_365, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_349])).
% 4.17/2.11  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_382, plain, (![A_88, E_84, F_86, D_89, B_85, C_87]: (k1_partfun1(A_88, B_85, C_87, D_89, E_84, F_86)=k5_relat_1(E_84, F_86) | ~m1_subset_1(F_86, k1_zfmisc_1(k2_zfmisc_1(C_87, D_89))) | ~v1_funct_1(F_86) | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_88, B_85))) | ~v1_funct_1(E_84))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.17/2.11  tff(c_390, plain, (![A_88, B_85, E_84]: (k1_partfun1(A_88, B_85, '#skF_2', '#skF_3', E_84, '#skF_5')=k5_relat_1(E_84, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_88, B_85))) | ~v1_funct_1(E_84))), inference(resolution, [status(thm)], [c_44, c_382])).
% 4.17/2.11  tff(c_716, plain, (![A_98, B_99, E_100]: (k1_partfun1(A_98, B_99, '#skF_2', '#skF_3', E_100, '#skF_5')=k5_relat_1(E_100, '#skF_5') | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_funct_1(E_100))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_390])).
% 4.17/2.11  tff(c_743, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_716])).
% 4.17/2.11  tff(c_756, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_743])).
% 4.17/2.11  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.17/2.11  tff(c_761, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_756, c_36])).
% 4.17/2.11  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_365, c_761])).
% 4.17/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/2.11  
% 4.17/2.11  Inference rules
% 4.17/2.11  ----------------------
% 4.17/2.11  #Ref     : 0
% 4.17/2.11  #Sup     : 180
% 4.17/2.11  #Fact    : 0
% 4.17/2.11  #Define  : 0
% 4.17/2.11  #Split   : 6
% 4.17/2.11  #Chain   : 0
% 4.17/2.11  #Close   : 0
% 4.17/2.11  
% 4.17/2.11  Ordering : KBO
% 4.17/2.11  
% 4.17/2.11  Simplification rules
% 4.17/2.11  ----------------------
% 4.17/2.11  #Subsume      : 5
% 4.17/2.11  #Demod        : 71
% 4.17/2.11  #Tautology    : 61
% 4.17/2.11  #SimpNegUnit  : 10
% 4.17/2.11  #BackRed      : 3
% 4.17/2.11  
% 4.17/2.11  #Partial instantiations: 0
% 4.17/2.11  #Strategies tried      : 1
% 4.17/2.11  
% 4.17/2.11  Timing (in seconds)
% 4.17/2.11  ----------------------
% 4.17/2.12  Preprocessing        : 0.55
% 4.17/2.12  Parsing              : 0.29
% 4.17/2.12  CNF conversion       : 0.04
% 4.17/2.12  Main loop            : 0.63
% 4.17/2.12  Inferencing          : 0.22
% 4.17/2.12  Reduction            : 0.21
% 4.17/2.12  Demodulation         : 0.15
% 4.17/2.12  BG Simplification    : 0.04
% 4.17/2.12  Subsumption          : 0.11
% 4.17/2.12  Abstraction          : 0.03
% 4.17/2.12  MUC search           : 0.00
% 4.17/2.12  Cooper               : 0.00
% 4.17/2.12  Total                : 1.25
% 4.17/2.12  Index Insertion      : 0.00
% 4.17/2.12  Index Deletion       : 0.00
% 4.17/2.12  Index Matching       : 0.00
% 4.17/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
