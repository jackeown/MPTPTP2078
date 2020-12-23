%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:43 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 117 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 338 expanded)
%              Number of equality atoms :   53 ( 132 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_34,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_102,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_110,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_158,plain,(
    ! [B_57,A_58,C_59] :
      ( k1_xboole_0 = B_57
      | k1_relset_1(A_58,B_57,C_59) = A_58
      | ~ v1_funct_2(C_59,A_58,B_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_161,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_167,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83,c_161])).

tff(c_168,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_167])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_176,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_2])).

tff(c_180,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_110,c_176])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_108,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_102])).

tff(c_112,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( k9_relat_1(B_4,k2_relat_1(A_2)) = k2_relat_1(k5_relat_1(A_2,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125,plain,(
    ! [B_4] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_4)) = k9_relat_1(B_4,'#skF_2')
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_4])).

tff(c_129,plain,(
    ! [B_4] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_4)) = k9_relat_1(B_4,'#skF_2')
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_125])).

tff(c_247,plain,(
    ! [C_67,B_68,F_72,E_70,A_71,D_69] :
      ( k4_relset_1(A_71,B_68,C_67,D_69,E_70,F_72) = k5_relat_1(E_70,F_72)
      | ~ m1_subset_1(F_72,k1_zfmisc_1(k2_zfmisc_1(C_67,D_69)))
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_254,plain,(
    ! [A_73,B_74,E_75] :
      ( k4_relset_1(A_73,B_74,'#skF_2','#skF_3',E_75,'#skF_5') = k5_relat_1(E_75,'#skF_5')
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_38,c_247])).

tff(c_262,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_254])).

tff(c_288,plain,(
    ! [F_79,D_84,B_82,E_81,C_83,A_80] :
      ( m1_subset_1(k4_relset_1(A_80,B_82,C_83,D_84,E_81,F_79),k1_zfmisc_1(k2_zfmisc_1(A_80,D_84)))
      | ~ m1_subset_1(F_79,k1_zfmisc_1(k2_zfmisc_1(C_83,D_84)))
      | ~ m1_subset_1(E_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_332,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_288])).

tff(c_352,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_332])).

tff(c_12,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_418,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_352,c_12])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_488,plain,(
    ! [A_87,D_85,F_88,C_90,E_89,B_86] :
      ( k1_partfun1(A_87,B_86,C_90,D_85,E_89,F_88) = k5_relat_1(E_89,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_90,D_85)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86)))
      | ~ v1_funct_1(E_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_500,plain,(
    ! [A_87,B_86,E_89] :
      ( k1_partfun1(A_87,B_86,'#skF_2','#skF_3',E_89,'#skF_5') = k5_relat_1(E_89,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86)))
      | ~ v1_funct_1(E_89) ) ),
    inference(resolution,[status(thm)],[c_38,c_488])).

tff(c_643,plain,(
    ! [A_94,B_95,E_96] :
      ( k1_partfun1(A_94,B_95,'#skF_2','#skF_3',E_96,'#skF_5') = k5_relat_1(E_96,'#skF_5')
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1(E_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_500])).

tff(c_667,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_643])).

tff(c_679,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_667])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_684,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_30])).

tff(c_685,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_684])).

tff(c_693,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_685])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_180,c_693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.55  
% 3.25/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.55  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.25/1.55  
% 3.25/1.55  %Foreground sorts:
% 3.25/1.55  
% 3.25/1.55  
% 3.25/1.55  %Background operators:
% 3.25/1.55  
% 3.25/1.55  
% 3.25/1.55  %Foreground operators:
% 3.25/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.25/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.55  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.55  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.55  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.25/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.25/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.55  
% 3.25/1.57  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 3.25/1.57  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.25/1.57  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.25/1.57  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.25/1.57  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.25/1.57  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.25/1.57  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.25/1.57  tff(f_60, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.25/1.57  tff(f_46, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.25/1.57  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.25/1.57  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_66, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.25/1.57  tff(c_73, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_66])).
% 3.25/1.57  tff(c_34, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_102, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.25/1.57  tff(c_105, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_102])).
% 3.25/1.57  tff(c_110, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_105])).
% 3.25/1.57  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_76, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.25/1.57  tff(c_83, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_76])).
% 3.25/1.57  tff(c_158, plain, (![B_57, A_58, C_59]: (k1_xboole_0=B_57 | k1_relset_1(A_58, B_57, C_59)=A_58 | ~v1_funct_2(C_59, A_58, B_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.25/1.57  tff(c_161, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_158])).
% 3.25/1.57  tff(c_167, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83, c_161])).
% 3.25/1.57  tff(c_168, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_167])).
% 3.25/1.57  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.57  tff(c_176, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_168, c_2])).
% 3.25/1.57  tff(c_180, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_110, c_176])).
% 3.25/1.57  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.25/1.57  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_108, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_102])).
% 3.25/1.57  tff(c_112, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108])).
% 3.25/1.57  tff(c_4, plain, (![B_4, A_2]: (k9_relat_1(B_4, k2_relat_1(A_2))=k2_relat_1(k5_relat_1(A_2, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.25/1.57  tff(c_125, plain, (![B_4]: (k2_relat_1(k5_relat_1('#skF_4', B_4))=k9_relat_1(B_4, '#skF_2') | ~v1_relat_1(B_4) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_4])).
% 3.25/1.57  tff(c_129, plain, (![B_4]: (k2_relat_1(k5_relat_1('#skF_4', B_4))=k9_relat_1(B_4, '#skF_2') | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_125])).
% 3.25/1.57  tff(c_247, plain, (![C_67, B_68, F_72, E_70, A_71, D_69]: (k4_relset_1(A_71, B_68, C_67, D_69, E_70, F_72)=k5_relat_1(E_70, F_72) | ~m1_subset_1(F_72, k1_zfmisc_1(k2_zfmisc_1(C_67, D_69))) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_68))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.57  tff(c_254, plain, (![A_73, B_74, E_75]: (k4_relset_1(A_73, B_74, '#skF_2', '#skF_3', E_75, '#skF_5')=k5_relat_1(E_75, '#skF_5') | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_38, c_247])).
% 3.25/1.57  tff(c_262, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_254])).
% 3.25/1.57  tff(c_288, plain, (![F_79, D_84, B_82, E_81, C_83, A_80]: (m1_subset_1(k4_relset_1(A_80, B_82, C_83, D_84, E_81, F_79), k1_zfmisc_1(k2_zfmisc_1(A_80, D_84))) | ~m1_subset_1(F_79, k1_zfmisc_1(k2_zfmisc_1(C_83, D_84))) | ~m1_subset_1(E_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_82))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.25/1.57  tff(c_332, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_262, c_288])).
% 3.25/1.57  tff(c_352, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_332])).
% 3.25/1.57  tff(c_12, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.25/1.57  tff(c_418, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_352, c_12])).
% 3.25/1.57  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_488, plain, (![A_87, D_85, F_88, C_90, E_89, B_86]: (k1_partfun1(A_87, B_86, C_90, D_85, E_89, F_88)=k5_relat_1(E_89, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_90, D_85))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))) | ~v1_funct_1(E_89))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.25/1.57  tff(c_500, plain, (![A_87, B_86, E_89]: (k1_partfun1(A_87, B_86, '#skF_2', '#skF_3', E_89, '#skF_5')=k5_relat_1(E_89, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))) | ~v1_funct_1(E_89))), inference(resolution, [status(thm)], [c_38, c_488])).
% 3.25/1.57  tff(c_643, plain, (![A_94, B_95, E_96]: (k1_partfun1(A_94, B_95, '#skF_2', '#skF_3', E_96, '#skF_5')=k5_relat_1(E_96, '#skF_5') | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1(E_96))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_500])).
% 3.25/1.57  tff(c_667, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_643])).
% 3.25/1.57  tff(c_679, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_667])).
% 3.25/1.57  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.57  tff(c_684, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_679, c_30])).
% 3.25/1.57  tff(c_685, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_418, c_684])).
% 3.25/1.57  tff(c_693, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_129, c_685])).
% 3.25/1.57  tff(c_696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_180, c_693])).
% 3.25/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.57  
% 3.25/1.57  Inference rules
% 3.25/1.57  ----------------------
% 3.25/1.57  #Ref     : 0
% 3.25/1.57  #Sup     : 175
% 3.25/1.57  #Fact    : 0
% 3.25/1.57  #Define  : 0
% 3.25/1.57  #Split   : 4
% 3.25/1.57  #Chain   : 0
% 3.25/1.57  #Close   : 0
% 3.25/1.57  
% 3.25/1.57  Ordering : KBO
% 3.25/1.57  
% 3.25/1.57  Simplification rules
% 3.25/1.57  ----------------------
% 3.25/1.57  #Subsume      : 0
% 3.25/1.57  #Demod        : 40
% 3.25/1.57  #Tautology    : 72
% 3.25/1.57  #SimpNegUnit  : 10
% 3.25/1.57  #BackRed      : 4
% 3.25/1.57  
% 3.25/1.57  #Partial instantiations: 0
% 3.25/1.57  #Strategies tried      : 1
% 3.25/1.57  
% 3.25/1.57  Timing (in seconds)
% 3.25/1.57  ----------------------
% 3.25/1.57  Preprocessing        : 0.37
% 3.25/1.57  Parsing              : 0.20
% 3.25/1.57  CNF conversion       : 0.02
% 3.25/1.57  Main loop            : 0.39
% 3.25/1.57  Inferencing          : 0.14
% 3.25/1.57  Reduction            : 0.12
% 3.25/1.57  Demodulation         : 0.08
% 3.25/1.57  BG Simplification    : 0.02
% 3.25/1.57  Subsumption          : 0.06
% 3.25/1.57  Abstraction          : 0.02
% 3.25/1.57  MUC search           : 0.00
% 3.25/1.57  Cooper               : 0.00
% 3.25/1.57  Total                : 0.79
% 3.25/1.57  Index Insertion      : 0.00
% 3.25/1.57  Index Deletion       : 0.00
% 3.25/1.57  Index Matching       : 0.00
% 3.25/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
