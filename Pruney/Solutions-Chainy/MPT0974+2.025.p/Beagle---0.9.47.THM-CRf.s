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
% DateTime   : Thu Dec  3 10:11:45 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 104 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 276 expanded)
%              Number of equality atoms :   38 (  99 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_99,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_77,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_125,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( k7_relset_1(A_49,B_50,C_51,D_52) = k9_relat_1(C_51,D_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    ! [D_52] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_52) = k9_relat_1('#skF_5',D_52) ),
    inference(resolution,[status(thm)],[c_30,c_125])).

tff(c_26,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_161,plain,(
    ! [A_58,B_59,C_60] :
      ( k7_relset_1(A_58,B_59,C_60,A_58) = k2_relset_1(A_58,B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_165,plain,(
    k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_2') = k2_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_169,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_26,c_165])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_71,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_66])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( k9_relat_1(B_8,k2_relat_1(A_6)) = k2_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [B_8] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_8)) = k9_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_6])).

tff(c_90,plain,(
    ! [B_8] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_8)) = k9_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_86])).

tff(c_206,plain,(
    ! [B_70,F_68,A_65,C_66,E_67,D_69] :
      ( k4_relset_1(A_65,B_70,C_66,D_69,E_67,F_68) = k5_relat_1(E_67,F_68)
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_66,D_69)))
      | ~ m1_subset_1(E_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_319,plain,(
    ! [A_80,B_81,E_82] :
      ( k4_relset_1(A_80,B_81,'#skF_2','#skF_3',E_82,'#skF_5') = k5_relat_1(E_82,'#skF_5')
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(resolution,[status(thm)],[c_30,c_206])).

tff(c_338,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_319])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] :
      ( m1_subset_1(k4_relset_1(A_9,B_10,C_11,D_12,E_13,F_14),k1_zfmisc_1(k2_zfmisc_1(A_9,D_12)))
      | ~ m1_subset_1(F_14,k1_zfmisc_1(k2_zfmisc_1(C_11,D_12)))
      | ~ m1_subset_1(E_13,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_343,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_8])).

tff(c_347,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_343])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_375,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_347,c_10])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_388,plain,(
    ! [B_84,E_85,F_87,D_83,C_88,A_86] :
      ( k1_partfun1(A_86,B_84,C_88,D_83,E_85,F_87) = k5_relat_1(E_85,F_87)
      | ~ m1_subset_1(F_87,k1_zfmisc_1(k2_zfmisc_1(C_88,D_83)))
      | ~ v1_funct_1(F_87)
      | ~ m1_subset_1(E_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_84)))
      | ~ v1_funct_1(E_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_400,plain,(
    ! [A_86,B_84,E_85] :
      ( k1_partfun1(A_86,B_84,'#skF_2','#skF_3',E_85,'#skF_5') = k5_relat_1(E_85,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_84)))
      | ~ v1_funct_1(E_85) ) ),
    inference(resolution,[status(thm)],[c_30,c_388])).

tff(c_629,plain,(
    ! [A_96,B_97,E_98] :
      ( k1_partfun1(A_96,B_97,'#skF_2','#skF_3',E_98,'#skF_5') = k5_relat_1(E_98,'#skF_5')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_400])).

tff(c_653,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_629])).

tff(c_666,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_653])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_670,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_22])).

tff(c_671,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_670])).

tff(c_678,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_671])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_169,c_678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.52  
% 2.71/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.52  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.82/1.52  
% 2.82/1.52  %Foreground sorts:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Background operators:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Foreground operators:
% 2.82/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.82/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.82/1.52  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.82/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.82/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.52  
% 2.84/1.54  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.84/1.54  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 2.84/1.54  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.84/1.54  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.84/1.54  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.84/1.54  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.84/1.54  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.84/1.54  tff(f_57, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.84/1.54  tff(f_47, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.84/1.54  tff(f_77, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.84/1.54  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.84/1.54  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.54  tff(c_50, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.54  tff(c_56, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_50])).
% 2.84/1.54  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_56])).
% 2.84/1.54  tff(c_125, plain, (![A_49, B_50, C_51, D_52]: (k7_relset_1(A_49, B_50, C_51, D_52)=k9_relat_1(C_51, D_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.54  tff(c_131, plain, (![D_52]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_52)=k9_relat_1('#skF_5', D_52))), inference(resolution, [status(thm)], [c_30, c_125])).
% 2.84/1.54  tff(c_26, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.54  tff(c_161, plain, (![A_58, B_59, C_60]: (k7_relset_1(A_58, B_59, C_60, A_58)=k2_relset_1(A_58, B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.54  tff(c_165, plain, (k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_2')=k2_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_161])).
% 2.84/1.54  tff(c_169, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_26, c_165])).
% 2.84/1.54  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.54  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_50])).
% 2.84/1.54  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_53])).
% 2.84/1.54  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.54  tff(c_63, plain, (![A_42, B_43, C_44]: (k2_relset_1(A_42, B_43, C_44)=k2_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.84/1.54  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_63])).
% 2.84/1.54  tff(c_71, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_66])).
% 2.84/1.54  tff(c_6, plain, (![B_8, A_6]: (k9_relat_1(B_8, k2_relat_1(A_6))=k2_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.54  tff(c_86, plain, (![B_8]: (k2_relat_1(k5_relat_1('#skF_4', B_8))=k9_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_6])).
% 2.84/1.54  tff(c_90, plain, (![B_8]: (k2_relat_1(k5_relat_1('#skF_4', B_8))=k9_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_86])).
% 2.84/1.54  tff(c_206, plain, (![B_70, F_68, A_65, C_66, E_67, D_69]: (k4_relset_1(A_65, B_70, C_66, D_69, E_67, F_68)=k5_relat_1(E_67, F_68) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_66, D_69))) | ~m1_subset_1(E_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_70))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.54  tff(c_319, plain, (![A_80, B_81, E_82]: (k4_relset_1(A_80, B_81, '#skF_2', '#skF_3', E_82, '#skF_5')=k5_relat_1(E_82, '#skF_5') | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(resolution, [status(thm)], [c_30, c_206])).
% 2.84/1.54  tff(c_338, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_319])).
% 2.84/1.54  tff(c_8, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (m1_subset_1(k4_relset_1(A_9, B_10, C_11, D_12, E_13, F_14), k1_zfmisc_1(k2_zfmisc_1(A_9, D_12))) | ~m1_subset_1(F_14, k1_zfmisc_1(k2_zfmisc_1(C_11, D_12))) | ~m1_subset_1(E_13, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.54  tff(c_343, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_338, c_8])).
% 2.84/1.54  tff(c_347, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_343])).
% 2.84/1.54  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.84/1.54  tff(c_375, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_347, c_10])).
% 2.84/1.54  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.54  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.54  tff(c_388, plain, (![B_84, E_85, F_87, D_83, C_88, A_86]: (k1_partfun1(A_86, B_84, C_88, D_83, E_85, F_87)=k5_relat_1(E_85, F_87) | ~m1_subset_1(F_87, k1_zfmisc_1(k2_zfmisc_1(C_88, D_83))) | ~v1_funct_1(F_87) | ~m1_subset_1(E_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_84))) | ~v1_funct_1(E_85))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.54  tff(c_400, plain, (![A_86, B_84, E_85]: (k1_partfun1(A_86, B_84, '#skF_2', '#skF_3', E_85, '#skF_5')=k5_relat_1(E_85, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_84))) | ~v1_funct_1(E_85))), inference(resolution, [status(thm)], [c_30, c_388])).
% 2.84/1.54  tff(c_629, plain, (![A_96, B_97, E_98]: (k1_partfun1(A_96, B_97, '#skF_2', '#skF_3', E_98, '#skF_5')=k5_relat_1(E_98, '#skF_5') | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_1(E_98))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_400])).
% 2.84/1.54  tff(c_653, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_629])).
% 2.84/1.54  tff(c_666, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_653])).
% 2.84/1.54  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.54  tff(c_670, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_666, c_22])).
% 2.84/1.54  tff(c_671, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_375, c_670])).
% 2.84/1.54  tff(c_678, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_671])).
% 2.84/1.54  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_169, c_678])).
% 2.84/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.54  
% 2.84/1.54  Inference rules
% 2.84/1.54  ----------------------
% 2.84/1.54  #Ref     : 0
% 2.84/1.54  #Sup     : 176
% 2.84/1.54  #Fact    : 0
% 2.84/1.54  #Define  : 0
% 2.84/1.54  #Split   : 0
% 2.84/1.54  #Chain   : 0
% 2.84/1.54  #Close   : 0
% 2.84/1.54  
% 2.84/1.54  Ordering : KBO
% 2.84/1.54  
% 2.84/1.54  Simplification rules
% 2.84/1.54  ----------------------
% 2.84/1.54  #Subsume      : 0
% 2.84/1.54  #Demod        : 39
% 2.84/1.54  #Tautology    : 64
% 2.84/1.54  #SimpNegUnit  : 0
% 2.84/1.54  #BackRed      : 1
% 2.84/1.54  
% 2.84/1.54  #Partial instantiations: 0
% 2.84/1.54  #Strategies tried      : 1
% 2.84/1.54  
% 2.84/1.54  Timing (in seconds)
% 2.84/1.54  ----------------------
% 2.84/1.54  Preprocessing        : 0.33
% 2.84/1.54  Parsing              : 0.16
% 2.84/1.54  CNF conversion       : 0.02
% 2.84/1.54  Main loop            : 0.33
% 2.84/1.54  Inferencing          : 0.13
% 2.84/1.54  Reduction            : 0.10
% 2.84/1.54  Demodulation         : 0.08
% 2.84/1.54  BG Simplification    : 0.02
% 2.84/1.54  Subsumption          : 0.05
% 2.84/1.54  Abstraction          : 0.02
% 2.84/1.54  MUC search           : 0.00
% 2.84/1.54  Cooper               : 0.00
% 2.84/1.54  Total                : 0.69
% 2.84/1.54  Index Insertion      : 0.00
% 2.84/1.54  Index Deletion       : 0.00
% 2.84/1.54  Index Matching       : 0.00
% 2.84/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
