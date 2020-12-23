%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:42 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 117 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 313 expanded)
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

tff(f_100,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_49,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_26,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_124,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_relset_1(A_49,B_50,C_51) = k2_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_127,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_132,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_127])).

tff(c_77,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_6])).

tff(c_91,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_105,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_101])).

tff(c_135,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_105])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_130,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_134,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_130])).

tff(c_153,plain,(
    ! [B_52,A_53] :
      ( k9_relat_1(B_52,k2_relat_1(A_53)) = k2_relat_1(k5_relat_1(A_53,B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_162,plain,(
    ! [B_52] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_52)) = k9_relat_1(B_52,'#skF_2')
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_153])).

tff(c_172,plain,(
    ! [B_52] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_52)) = k9_relat_1(B_52,'#skF_2')
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_162])).

tff(c_233,plain,(
    ! [A_66,B_64,C_61,E_63,D_65,F_62] :
      ( k4_relset_1(A_66,B_64,C_61,D_65,E_63,F_62) = k5_relat_1(E_63,F_62)
      | ~ m1_subset_1(F_62,k1_zfmisc_1(k2_zfmisc_1(C_61,D_65)))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(A_66,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_240,plain,(
    ! [A_67,B_68,E_69] :
      ( k4_relset_1(A_67,B_68,'#skF_2','#skF_3',E_69,'#skF_5') = k5_relat_1(E_69,'#skF_5')
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(resolution,[status(thm)],[c_30,c_233])).

tff(c_248,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_240])).

tff(c_286,plain,(
    ! [C_78,D_77,B_79,F_76,A_80,E_75] :
      ( m1_subset_1(k4_relset_1(A_80,B_79,C_78,D_77,E_75,F_76),k1_zfmisc_1(k2_zfmisc_1(A_80,D_77)))
      | ~ m1_subset_1(F_76,k1_zfmisc_1(k2_zfmisc_1(C_78,D_77)))
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_315,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_286])).

tff(c_331,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_315])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22] :
      ( k2_relset_1(A_20,B_21,C_22) = k2_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_455,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_331,c_16])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_361,plain,(
    ! [F_84,D_81,C_86,B_82,A_83,E_85] :
      ( k1_partfun1(A_83,B_82,C_86,D_81,E_85,F_84) = k5_relat_1(E_85,F_84)
      | ~ m1_subset_1(F_84,k1_zfmisc_1(k2_zfmisc_1(C_86,D_81)))
      | ~ v1_funct_1(F_84)
      | ~ m1_subset_1(E_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_1(E_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_367,plain,(
    ! [A_83,B_82,E_85] :
      ( k1_partfun1(A_83,B_82,'#skF_2','#skF_3',E_85,'#skF_5') = k5_relat_1(E_85,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_1(E_85) ) ),
    inference(resolution,[status(thm)],[c_30,c_361])).

tff(c_552,plain,(
    ! [A_90,B_91,E_92] :
      ( k1_partfun1(A_90,B_91,'#skF_2','#skF_3',E_92,'#skF_5') = k5_relat_1(E_92,'#skF_5')
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(E_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_367])).

tff(c_573,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_552])).

tff(c_584,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_573])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_673,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_22])).

tff(c_721,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_673])).

tff(c_728,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_721])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_135,c_728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.51  
% 2.69/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.69/1.51  
% 2.69/1.51  %Foreground sorts:
% 2.69/1.51  
% 2.69/1.51  
% 2.69/1.51  %Background operators:
% 2.69/1.51  
% 2.69/1.51  
% 2.69/1.51  %Foreground operators:
% 2.69/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.69/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.69/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.69/1.51  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.69/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.51  
% 2.69/1.52  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 2.69/1.52  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.52  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.69/1.52  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.69/1.52  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.69/1.52  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.69/1.52  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.69/1.52  tff(f_68, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.69/1.52  tff(f_58, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.69/1.52  tff(f_78, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.69/1.52  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_49, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.52  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_49])).
% 2.69/1.52  tff(c_26, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_124, plain, (![A_49, B_50, C_51]: (k2_relset_1(A_49, B_50, C_51)=k2_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.52  tff(c_127, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_124])).
% 2.69/1.52  tff(c_132, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_127])).
% 2.69/1.52  tff(c_77, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.52  tff(c_84, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_77])).
% 2.69/1.52  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.52  tff(c_88, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_6])).
% 2.69/1.52  tff(c_91, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88])).
% 2.69/1.52  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.52  tff(c_101, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 2.69/1.52  tff(c_105, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_101])).
% 2.69/1.52  tff(c_135, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_105])).
% 2.69/1.52  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_49])).
% 2.69/1.52  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_130, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_124])).
% 2.69/1.52  tff(c_134, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_130])).
% 2.69/1.52  tff(c_153, plain, (![B_52, A_53]: (k9_relat_1(B_52, k2_relat_1(A_53))=k2_relat_1(k5_relat_1(A_53, B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.52  tff(c_162, plain, (![B_52]: (k2_relat_1(k5_relat_1('#skF_4', B_52))=k9_relat_1(B_52, '#skF_2') | ~v1_relat_1(B_52) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_153])).
% 2.69/1.52  tff(c_172, plain, (![B_52]: (k2_relat_1(k5_relat_1('#skF_4', B_52))=k9_relat_1(B_52, '#skF_2') | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_162])).
% 2.69/1.52  tff(c_233, plain, (![A_66, B_64, C_61, E_63, D_65, F_62]: (k4_relset_1(A_66, B_64, C_61, D_65, E_63, F_62)=k5_relat_1(E_63, F_62) | ~m1_subset_1(F_62, k1_zfmisc_1(k2_zfmisc_1(C_61, D_65))) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(A_66, B_64))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.52  tff(c_240, plain, (![A_67, B_68, E_69]: (k4_relset_1(A_67, B_68, '#skF_2', '#skF_3', E_69, '#skF_5')=k5_relat_1(E_69, '#skF_5') | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(resolution, [status(thm)], [c_30, c_233])).
% 2.69/1.52  tff(c_248, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_240])).
% 2.69/1.52  tff(c_286, plain, (![C_78, D_77, B_79, F_76, A_80, E_75]: (m1_subset_1(k4_relset_1(A_80, B_79, C_78, D_77, E_75, F_76), k1_zfmisc_1(k2_zfmisc_1(A_80, D_77))) | ~m1_subset_1(F_76, k1_zfmisc_1(k2_zfmisc_1(C_78, D_77))) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.52  tff(c_315, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_248, c_286])).
% 2.69/1.52  tff(c_331, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_315])).
% 2.69/1.52  tff(c_16, plain, (![A_20, B_21, C_22]: (k2_relset_1(A_20, B_21, C_22)=k2_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.52  tff(c_455, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_331, c_16])).
% 2.69/1.52  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_361, plain, (![F_84, D_81, C_86, B_82, A_83, E_85]: (k1_partfun1(A_83, B_82, C_86, D_81, E_85, F_84)=k5_relat_1(E_85, F_84) | ~m1_subset_1(F_84, k1_zfmisc_1(k2_zfmisc_1(C_86, D_81))) | ~v1_funct_1(F_84) | ~m1_subset_1(E_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_1(E_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.52  tff(c_367, plain, (![A_83, B_82, E_85]: (k1_partfun1(A_83, B_82, '#skF_2', '#skF_3', E_85, '#skF_5')=k5_relat_1(E_85, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_1(E_85))), inference(resolution, [status(thm)], [c_30, c_361])).
% 2.69/1.52  tff(c_552, plain, (![A_90, B_91, E_92]: (k1_partfun1(A_90, B_91, '#skF_2', '#skF_3', E_92, '#skF_5')=k5_relat_1(E_92, '#skF_5') | ~m1_subset_1(E_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(E_92))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_367])).
% 2.69/1.52  tff(c_573, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_552])).
% 2.69/1.52  tff(c_584, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_573])).
% 2.69/1.52  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_673, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_584, c_22])).
% 2.69/1.52  tff(c_721, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_455, c_673])).
% 2.69/1.52  tff(c_728, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_172, c_721])).
% 2.69/1.52  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_135, c_728])).
% 2.69/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.52  
% 2.69/1.52  Inference rules
% 2.69/1.52  ----------------------
% 2.69/1.52  #Ref     : 0
% 2.69/1.52  #Sup     : 192
% 2.69/1.52  #Fact    : 0
% 2.69/1.52  #Define  : 0
% 2.69/1.52  #Split   : 0
% 2.69/1.52  #Chain   : 0
% 2.69/1.52  #Close   : 0
% 2.69/1.52  
% 2.69/1.52  Ordering : KBO
% 2.69/1.52  
% 2.69/1.52  Simplification rules
% 2.69/1.52  ----------------------
% 2.69/1.52  #Subsume      : 2
% 2.69/1.52  #Demod        : 62
% 2.69/1.52  #Tautology    : 78
% 2.69/1.52  #SimpNegUnit  : 0
% 2.69/1.52  #BackRed      : 4
% 2.69/1.52  
% 2.69/1.52  #Partial instantiations: 0
% 2.69/1.52  #Strategies tried      : 1
% 2.69/1.52  
% 2.69/1.52  Timing (in seconds)
% 2.69/1.52  ----------------------
% 2.69/1.53  Preprocessing        : 0.30
% 2.69/1.53  Parsing              : 0.16
% 2.69/1.53  CNF conversion       : 0.02
% 2.69/1.53  Main loop            : 0.36
% 2.69/1.53  Inferencing          : 0.14
% 2.69/1.53  Reduction            : 0.11
% 2.69/1.53  Demodulation         : 0.08
% 2.69/1.53  BG Simplification    : 0.02
% 2.69/1.53  Subsumption          : 0.06
% 2.69/1.53  Abstraction          : 0.02
% 2.69/1.53  MUC search           : 0.00
% 2.69/1.53  Cooper               : 0.00
% 2.69/1.53  Total                : 0.69
% 2.69/1.53  Index Insertion      : 0.00
% 2.69/1.53  Index Deletion       : 0.00
% 2.69/1.53  Index Matching       : 0.00
% 2.69/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
