%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:44 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 129 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 337 expanded)
%              Number of equality atoms :   41 ( 112 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_105,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_28,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_143,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_149,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_143])).

tff(c_153,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_149])).

tff(c_84,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_10])).

tff(c_104,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_101])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6])).

tff(c_121,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_117])).

tff(c_164,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_121])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_55,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_55])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_146,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_143])).

tff(c_151,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_146])).

tff(c_8,plain,(
    ! [B_10,A_8] :
      ( k9_relat_1(B_10,k2_relat_1(A_8)) = k2_relat_1(k5_relat_1(A_8,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_158,plain,(
    ! [B_10] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_10)) = k9_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_8])).

tff(c_162,plain,(
    ! [B_10] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_10)) = k9_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_158])).

tff(c_228,plain,(
    ! [B_66,D_62,A_63,F_65,C_64,E_67] :
      ( k4_relset_1(A_63,B_66,C_64,D_62,E_67,F_65) = k5_relat_1(E_67,F_65)
      | ~ m1_subset_1(F_65,k1_zfmisc_1(k2_zfmisc_1(C_64,D_62)))
      | ~ m1_subset_1(E_67,k1_zfmisc_1(k2_zfmisc_1(A_63,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_252,plain,(
    ! [A_71,B_72,E_73] :
      ( k4_relset_1(A_71,B_72,'#skF_2','#skF_3',E_73,'#skF_5') = k5_relat_1(E_73,'#skF_5')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(resolution,[status(thm)],[c_32,c_228])).

tff(c_259,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_252])).

tff(c_293,plain,(
    ! [E_80,A_81,B_79,F_78,C_83,D_82] :
      ( m1_subset_1(k4_relset_1(A_81,B_79,C_83,D_82,E_80,F_78),k1_zfmisc_1(k2_zfmisc_1(A_81,D_82)))
      | ~ m1_subset_1(F_78,k1_zfmisc_1(k2_zfmisc_1(C_83,D_82)))
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_319,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_293])).

tff(c_338,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_319])).

tff(c_18,plain,(
    ! [A_22,B_23,C_24] :
      ( k2_relset_1(A_22,B_23,C_24) = k2_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_497,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_338,c_18])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_343,plain,(
    ! [A_87,C_89,D_84,F_88,B_85,E_86] :
      ( k1_partfun1(A_87,B_85,C_89,D_84,E_86,F_88) = k5_relat_1(E_86,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_89,D_84)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_85)))
      | ~ v1_funct_1(E_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_349,plain,(
    ! [A_87,B_85,E_86] :
      ( k1_partfun1(A_87,B_85,'#skF_2','#skF_3',E_86,'#skF_5') = k5_relat_1(E_86,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_85)))
      | ~ v1_funct_1(E_86) ) ),
    inference(resolution,[status(thm)],[c_32,c_343])).

tff(c_555,plain,(
    ! [A_93,B_94,E_95] :
      ( k1_partfun1(A_93,B_94,'#skF_2','#skF_3',E_95,'#skF_5') = k5_relat_1(E_95,'#skF_5')
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1(E_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_349])).

tff(c_573,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_555])).

tff(c_584,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_573])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_690,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_24])).

tff(c_727,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_690])).

tff(c_734,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_727])).

tff(c_737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_164,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:08:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.84/1.43  
% 2.84/1.43  %Foreground sorts:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Background operators:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Foreground operators:
% 2.84/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.84/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.84/1.43  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.84/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.84/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.84/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.43  
% 3.10/1.45  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.10/1.45  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.10/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.10/1.45  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.45  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.45  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.10/1.45  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.10/1.45  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.10/1.45  tff(f_73, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.10/1.45  tff(f_63, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.10/1.45  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.10/1.45  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.45  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.10/1.45  tff(c_52, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.45  tff(c_58, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_52])).
% 3.10/1.45  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_58])).
% 3.10/1.45  tff(c_28, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.10/1.45  tff(c_143, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.45  tff(c_149, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_143])).
% 3.10/1.45  tff(c_153, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_149])).
% 3.10/1.45  tff(c_84, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.45  tff(c_92, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_84])).
% 3.10/1.45  tff(c_10, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.45  tff(c_101, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_10])).
% 3.10/1.45  tff(c_104, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_101])).
% 3.10/1.45  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.10/1.45  tff(c_117, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_104, c_6])).
% 3.10/1.45  tff(c_121, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_117])).
% 3.10/1.45  tff(c_164, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_121])).
% 3.10/1.45  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.10/1.45  tff(c_55, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_52])).
% 3.10/1.45  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_55])).
% 3.10/1.45  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.10/1.45  tff(c_146, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_143])).
% 3.10/1.45  tff(c_151, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_146])).
% 3.10/1.45  tff(c_8, plain, (![B_10, A_8]: (k9_relat_1(B_10, k2_relat_1(A_8))=k2_relat_1(k5_relat_1(A_8, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.10/1.45  tff(c_158, plain, (![B_10]: (k2_relat_1(k5_relat_1('#skF_4', B_10))=k9_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_8])).
% 3.10/1.45  tff(c_162, plain, (![B_10]: (k2_relat_1(k5_relat_1('#skF_4', B_10))=k9_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_158])).
% 3.10/1.45  tff(c_228, plain, (![B_66, D_62, A_63, F_65, C_64, E_67]: (k4_relset_1(A_63, B_66, C_64, D_62, E_67, F_65)=k5_relat_1(E_67, F_65) | ~m1_subset_1(F_65, k1_zfmisc_1(k2_zfmisc_1(C_64, D_62))) | ~m1_subset_1(E_67, k1_zfmisc_1(k2_zfmisc_1(A_63, B_66))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.10/1.45  tff(c_252, plain, (![A_71, B_72, E_73]: (k4_relset_1(A_71, B_72, '#skF_2', '#skF_3', E_73, '#skF_5')=k5_relat_1(E_73, '#skF_5') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(resolution, [status(thm)], [c_32, c_228])).
% 3.10/1.45  tff(c_259, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_252])).
% 3.10/1.45  tff(c_293, plain, (![E_80, A_81, B_79, F_78, C_83, D_82]: (m1_subset_1(k4_relset_1(A_81, B_79, C_83, D_82, E_80, F_78), k1_zfmisc_1(k2_zfmisc_1(A_81, D_82))) | ~m1_subset_1(F_78, k1_zfmisc_1(k2_zfmisc_1(C_83, D_82))) | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_79))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.10/1.45  tff(c_319, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_259, c_293])).
% 3.10/1.45  tff(c_338, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_319])).
% 3.10/1.45  tff(c_18, plain, (![A_22, B_23, C_24]: (k2_relset_1(A_22, B_23, C_24)=k2_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.45  tff(c_497, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_338, c_18])).
% 3.10/1.45  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.10/1.45  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.10/1.45  tff(c_343, plain, (![A_87, C_89, D_84, F_88, B_85, E_86]: (k1_partfun1(A_87, B_85, C_89, D_84, E_86, F_88)=k5_relat_1(E_86, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_89, D_84))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_85))) | ~v1_funct_1(E_86))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.45  tff(c_349, plain, (![A_87, B_85, E_86]: (k1_partfun1(A_87, B_85, '#skF_2', '#skF_3', E_86, '#skF_5')=k5_relat_1(E_86, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_85))) | ~v1_funct_1(E_86))), inference(resolution, [status(thm)], [c_32, c_343])).
% 3.10/1.45  tff(c_555, plain, (![A_93, B_94, E_95]: (k1_partfun1(A_93, B_94, '#skF_2', '#skF_3', E_95, '#skF_5')=k5_relat_1(E_95, '#skF_5') | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1(E_95))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_349])).
% 3.10/1.45  tff(c_573, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_555])).
% 3.10/1.45  tff(c_584, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_573])).
% 3.10/1.45  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.10/1.45  tff(c_690, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_584, c_24])).
% 3.10/1.45  tff(c_727, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_497, c_690])).
% 3.10/1.45  tff(c_734, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_162, c_727])).
% 3.10/1.45  tff(c_737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_164, c_734])).
% 3.10/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.45  
% 3.10/1.45  Inference rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Ref     : 0
% 3.10/1.45  #Sup     : 186
% 3.10/1.45  #Fact    : 0
% 3.10/1.45  #Define  : 0
% 3.10/1.45  #Split   : 0
% 3.10/1.45  #Chain   : 0
% 3.10/1.45  #Close   : 0
% 3.10/1.45  
% 3.10/1.45  Ordering : KBO
% 3.10/1.45  
% 3.10/1.45  Simplification rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Subsume      : 2
% 3.10/1.45  #Demod        : 70
% 3.10/1.45  #Tautology    : 72
% 3.10/1.45  #SimpNegUnit  : 0
% 3.10/1.45  #BackRed      : 4
% 3.10/1.45  
% 3.10/1.45  #Partial instantiations: 0
% 3.10/1.45  #Strategies tried      : 1
% 3.10/1.45  
% 3.10/1.45  Timing (in seconds)
% 3.10/1.45  ----------------------
% 3.10/1.45  Preprocessing        : 0.32
% 3.10/1.45  Parsing              : 0.18
% 3.10/1.45  CNF conversion       : 0.02
% 3.10/1.45  Main loop            : 0.36
% 3.10/1.45  Inferencing          : 0.14
% 3.10/1.45  Reduction            : 0.11
% 3.10/1.45  Demodulation         : 0.08
% 3.10/1.45  BG Simplification    : 0.02
% 3.10/1.45  Subsumption          : 0.05
% 3.10/1.45  Abstraction          : 0.02
% 3.10/1.45  MUC search           : 0.00
% 3.10/1.45  Cooper               : 0.00
% 3.10/1.45  Total                : 0.71
% 3.10/1.45  Index Insertion      : 0.00
% 3.10/1.45  Index Deletion       : 0.00
% 3.10/1.45  Index Matching       : 0.00
% 3.10/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
