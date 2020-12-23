%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:42 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 111 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 325 expanded)
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

tff(f_114,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_96,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_104,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_99])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_79,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_144,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_144])).

tff(c_153,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_86,c_147])).

tff(c_154,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_153])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_40,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_102,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_106,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_102])).

tff(c_117,plain,(
    ! [B_52,A_53] :
      ( k2_relat_1(k5_relat_1(B_52,A_53)) = k2_relat_1(A_53)
      | ~ r1_tarski(k1_relat_1(A_53),k2_relat_1(B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,(
    ! [A_53] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_53)) = k2_relat_1(A_53)
      | ~ r1_tarski(k1_relat_1(A_53),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_117])).

tff(c_125,plain,(
    ! [A_53] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_53)) = k2_relat_1(A_53)
      | ~ r1_tarski(k1_relat_1(A_53),'#skF_2')
      | ~ v1_relat_1(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_120])).

tff(c_165,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_125])).

tff(c_174,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6,c_104,c_165])).

tff(c_207,plain,(
    ! [B_70,A_66,D_67,C_68,F_69,E_71] :
      ( k4_relset_1(A_66,B_70,C_68,D_67,E_71,F_69) = k5_relat_1(E_71,F_69)
      | ~ m1_subset_1(F_69,k1_zfmisc_1(k2_zfmisc_1(C_68,D_67)))
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_66,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_321,plain,(
    ! [A_81,B_82,E_83] :
      ( k4_relset_1(A_81,B_82,'#skF_2','#skF_3',E_83,'#skF_5') = k5_relat_1(E_83,'#skF_5')
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(resolution,[status(thm)],[c_42,c_207])).

tff(c_337,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_321])).

tff(c_12,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] :
      ( m1_subset_1(k4_relset_1(A_9,B_10,C_11,D_12,E_13,F_14),k1_zfmisc_1(k2_zfmisc_1(A_9,D_12)))
      | ~ m1_subset_1(F_14,k1_zfmisc_1(k2_zfmisc_1(C_11,D_12)))
      | ~ m1_subset_1(E_13,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_439,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_12])).

tff(c_443,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_439])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_463,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_443,c_16])).

tff(c_481,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_463])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_413,plain,(
    ! [A_87,E_88,F_86,C_84,D_89,B_85] :
      ( k1_partfun1(A_87,B_85,C_84,D_89,E_88,F_86) = k5_relat_1(E_88,F_86)
      | ~ m1_subset_1(F_86,k1_zfmisc_1(k2_zfmisc_1(C_84,D_89)))
      | ~ v1_funct_1(F_86)
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_87,B_85)))
      | ~ v1_funct_1(E_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_423,plain,(
    ! [A_87,B_85,E_88] :
      ( k1_partfun1(A_87,B_85,'#skF_2','#skF_3',E_88,'#skF_5') = k5_relat_1(E_88,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_87,B_85)))
      | ~ v1_funct_1(E_88) ) ),
    inference(resolution,[status(thm)],[c_42,c_413])).

tff(c_576,plain,(
    ! [A_94,B_95,E_96] :
      ( k1_partfun1(A_94,B_95,'#skF_2','#skF_3',E_96,'#skF_5') = k5_relat_1(E_96,'#skF_5')
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1(E_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_423])).

tff(c_597,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_576])).

tff(c_608,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_597])).

tff(c_34,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_613,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_34])).

tff(c_616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:46:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.78/1.39  
% 2.78/1.39  %Foreground sorts:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Background operators:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Foreground operators:
% 2.78/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.39  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.39  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.78/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.39  
% 2.78/1.41  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 2.78/1.41  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.78/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.41  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.78/1.41  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.78/1.41  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.78/1.41  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.78/1.41  tff(f_64, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.78/1.41  tff(f_50, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.78/1.41  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.78/1.41  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_70, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.78/1.41  tff(c_77, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_70])).
% 2.78/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.41  tff(c_38, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_96, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.78/1.41  tff(c_99, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_96])).
% 2.78/1.41  tff(c_104, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_99])).
% 2.78/1.41  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_79, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.41  tff(c_86, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_79])).
% 2.78/1.41  tff(c_144, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.41  tff(c_147, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_144])).
% 2.78/1.41  tff(c_153, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_86, c_147])).
% 2.78/1.41  tff(c_154, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_153])).
% 2.78/1.41  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_70])).
% 2.78/1.41  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_102, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_96])).
% 2.78/1.41  tff(c_106, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_102])).
% 2.78/1.41  tff(c_117, plain, (![B_52, A_53]: (k2_relat_1(k5_relat_1(B_52, A_53))=k2_relat_1(A_53) | ~r1_tarski(k1_relat_1(A_53), k2_relat_1(B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.41  tff(c_120, plain, (![A_53]: (k2_relat_1(k5_relat_1('#skF_4', A_53))=k2_relat_1(A_53) | ~r1_tarski(k1_relat_1(A_53), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_106, c_117])).
% 2.78/1.41  tff(c_125, plain, (![A_53]: (k2_relat_1(k5_relat_1('#skF_4', A_53))=k2_relat_1(A_53) | ~r1_tarski(k1_relat_1(A_53), '#skF_2') | ~v1_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_120])).
% 2.78/1.41  tff(c_165, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_154, c_125])).
% 2.78/1.41  tff(c_174, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6, c_104, c_165])).
% 2.78/1.41  tff(c_207, plain, (![B_70, A_66, D_67, C_68, F_69, E_71]: (k4_relset_1(A_66, B_70, C_68, D_67, E_71, F_69)=k5_relat_1(E_71, F_69) | ~m1_subset_1(F_69, k1_zfmisc_1(k2_zfmisc_1(C_68, D_67))) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_66, B_70))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.78/1.41  tff(c_321, plain, (![A_81, B_82, E_83]: (k4_relset_1(A_81, B_82, '#skF_2', '#skF_3', E_83, '#skF_5')=k5_relat_1(E_83, '#skF_5') | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(resolution, [status(thm)], [c_42, c_207])).
% 2.78/1.41  tff(c_337, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_321])).
% 2.78/1.41  tff(c_12, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (m1_subset_1(k4_relset_1(A_9, B_10, C_11, D_12, E_13, F_14), k1_zfmisc_1(k2_zfmisc_1(A_9, D_12))) | ~m1_subset_1(F_14, k1_zfmisc_1(k2_zfmisc_1(C_11, D_12))) | ~m1_subset_1(E_13, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.78/1.41  tff(c_439, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_337, c_12])).
% 2.78/1.41  tff(c_443, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_439])).
% 2.78/1.41  tff(c_16, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.78/1.41  tff(c_463, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_443, c_16])).
% 2.78/1.41  tff(c_481, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_463])).
% 2.78/1.41  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_413, plain, (![A_87, E_88, F_86, C_84, D_89, B_85]: (k1_partfun1(A_87, B_85, C_84, D_89, E_88, F_86)=k5_relat_1(E_88, F_86) | ~m1_subset_1(F_86, k1_zfmisc_1(k2_zfmisc_1(C_84, D_89))) | ~v1_funct_1(F_86) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_87, B_85))) | ~v1_funct_1(E_88))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.78/1.41  tff(c_423, plain, (![A_87, B_85, E_88]: (k1_partfun1(A_87, B_85, '#skF_2', '#skF_3', E_88, '#skF_5')=k5_relat_1(E_88, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_87, B_85))) | ~v1_funct_1(E_88))), inference(resolution, [status(thm)], [c_42, c_413])).
% 2.78/1.41  tff(c_576, plain, (![A_94, B_95, E_96]: (k1_partfun1(A_94, B_95, '#skF_2', '#skF_3', E_96, '#skF_5')=k5_relat_1(E_96, '#skF_5') | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1(E_96))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_423])).
% 2.78/1.41  tff(c_597, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_576])).
% 2.78/1.41  tff(c_608, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_597])).
% 2.78/1.41  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.78/1.41  tff(c_613, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_34])).
% 2.78/1.41  tff(c_616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_613])).
% 2.78/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  Inference rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Ref     : 0
% 2.78/1.41  #Sup     : 149
% 2.78/1.41  #Fact    : 0
% 2.78/1.41  #Define  : 0
% 2.78/1.41  #Split   : 6
% 2.78/1.41  #Chain   : 0
% 2.78/1.41  #Close   : 0
% 2.78/1.41  
% 2.78/1.41  Ordering : KBO
% 2.78/1.41  
% 2.78/1.41  Simplification rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Subsume      : 2
% 2.78/1.41  #Demod        : 52
% 2.78/1.41  #Tautology    : 57
% 2.78/1.41  #SimpNegUnit  : 6
% 2.78/1.41  #BackRed      : 3
% 2.78/1.41  
% 2.78/1.41  #Partial instantiations: 0
% 2.78/1.41  #Strategies tried      : 1
% 2.78/1.41  
% 2.78/1.41  Timing (in seconds)
% 2.78/1.41  ----------------------
% 2.78/1.41  Preprocessing        : 0.32
% 2.78/1.41  Parsing              : 0.17
% 2.78/1.41  CNF conversion       : 0.02
% 2.78/1.41  Main loop            : 0.32
% 2.78/1.41  Inferencing          : 0.11
% 2.78/1.41  Reduction            : 0.10
% 2.78/1.41  Demodulation         : 0.07
% 2.78/1.41  BG Simplification    : 0.02
% 2.78/1.41  Subsumption          : 0.06
% 2.78/1.41  Abstraction          : 0.02
% 2.78/1.41  MUC search           : 0.00
% 2.78/1.41  Cooper               : 0.00
% 2.78/1.41  Total                : 0.67
% 2.78/1.41  Index Insertion      : 0.00
% 2.78/1.41  Index Deletion       : 0.00
% 2.78/1.41  Index Matching       : 0.00
% 2.78/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
