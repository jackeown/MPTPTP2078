%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:03 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 886 expanded)
%              Number of leaves         :   28 ( 312 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 (1434 expanded)
%              Number of equality atoms :   45 ( 504 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_39])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_37])).

tff(c_96,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_96])).

tff(c_105,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_2])).

tff(c_111,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105,c_44])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_12])).

tff(c_125,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_58])).

tff(c_61,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_43,c_10])).

tff(c_123,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_111,c_61])).

tff(c_178,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_partfun1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_184,plain,(
    ! [C_42] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_178])).

tff(c_204,plain,(
    ! [C_52] :
      ( v1_partfun1(C_52,'#skF_4')
      | ~ m1_subset_1(C_52,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_184])).

tff(c_209,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_125,c_204])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_231,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_funct_2(C_58,A_59,B_60)
      | ~ v1_partfun1(C_58,A_59)
      | ~ v1_funct_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_241,plain,(
    ! [A_59,B_60] :
      ( v1_funct_2('#skF_4',A_59,B_60)
      | ~ v1_partfun1('#skF_4',A_59)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125,c_231])).

tff(c_244,plain,(
    ! [A_59,B_60] :
      ( v1_funct_2('#skF_4',A_59,B_60)
      | ~ v1_partfun1('#skF_4',A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_241])).

tff(c_195,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( k8_relset_1(A_48,B_49,C_50,D_51) = k10_relat_1(C_50,D_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_203,plain,(
    ! [A_48,B_49,D_51] : k8_relset_1(A_48,B_49,'#skF_4',D_51) = k10_relat_1('#skF_4',D_51) ),
    inference(resolution,[status(thm)],[c_125,c_195])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_43])).

tff(c_26,plain,(
    ! [B_23,C_24] :
      ( k8_relset_1(k1_xboole_0,B_23,C_24,B_23) = k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23)))
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [B_23,C_24] :
      ( k8_relset_1(k1_xboole_0,B_23,C_24,B_23) = k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_308,plain,(
    ! [B_73,C_74] :
      ( k8_relset_1('#skF_4',B_73,C_74,B_73) = '#skF_4'
      | ~ m1_subset_1(C_74,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(C_74,'#skF_4',B_73)
      | ~ v1_funct_1(C_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_127,c_127,c_127,c_38])).

tff(c_311,plain,(
    ! [B_73] :
      ( k8_relset_1('#skF_4',B_73,'#skF_4',B_73) = '#skF_4'
      | ~ v1_funct_2('#skF_4','#skF_4',B_73)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125,c_308])).

tff(c_325,plain,(
    ! [B_75] :
      ( k10_relat_1('#skF_4',B_75) = '#skF_4'
      | ~ v1_funct_2('#skF_4','#skF_4',B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_203,c_311])).

tff(c_329,plain,(
    ! [B_60] :
      ( k10_relat_1('#skF_4',B_60) = '#skF_4'
      | ~ v1_partfun1('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_244,c_325])).

tff(c_335,plain,(
    ! [B_60] : k10_relat_1('#skF_4',B_60) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_329])).

tff(c_28,plain,(
    ! [B_23,A_22,C_24] :
      ( k1_xboole_0 = B_23
      | k8_relset_1(A_22,B_23,C_24,B_23) = A_22
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_252,plain,(
    ! [B_65,A_66,C_67] :
      ( B_65 = '#skF_4'
      | k8_relset_1(A_66,B_65,C_67,B_65) = A_66
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65)))
      | ~ v1_funct_2(C_67,A_66,B_65)
      | ~ v1_funct_1(C_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_259,plain,(
    ! [B_65,A_66] :
      ( B_65 = '#skF_4'
      | k8_relset_1(A_66,B_65,'#skF_4',B_65) = A_66
      | ~ v1_funct_2('#skF_4',A_66,B_65)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125,c_252])).

tff(c_264,plain,(
    ! [B_68,A_69] :
      ( B_68 = '#skF_4'
      | k10_relat_1('#skF_4',B_68) = A_69
      | ~ v1_funct_2('#skF_4',A_69,B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_203,c_259])).

tff(c_278,plain,(
    ! [B_70,A_71] :
      ( B_70 = '#skF_4'
      | k10_relat_1('#skF_4',B_70) = A_71
      | ~ v1_partfun1('#skF_4',A_71) ) ),
    inference(resolution,[status(thm)],[c_244,c_264])).

tff(c_286,plain,(
    ! [B_72] :
      ( B_72 = '#skF_4'
      | k10_relat_1('#skF_4',B_72) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_209,c_278])).

tff(c_30,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_77,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_43,c_30])).

tff(c_122,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_111,c_77])).

tff(c_221,plain,(
    k10_relat_1('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_122])).

tff(c_304,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_221])).

tff(c_315,plain,(
    k10_relat_1('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_221])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.27  
% 2.34/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.27  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.34/1.27  
% 2.34/1.27  %Foreground sorts:
% 2.34/1.27  
% 2.34/1.27  
% 2.34/1.27  %Background operators:
% 2.34/1.27  
% 2.34/1.27  
% 2.34/1.27  %Foreground operators:
% 2.34/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.27  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.34/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.34/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.34/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.27  
% 2.34/1.29  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.34/1.29  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.34/1.29  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.34/1.29  tff(f_94, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.34/1.29  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.34/1.29  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.34/1.29  tff(f_73, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.34/1.29  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.34/1.29  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.34/1.29  tff(f_85, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.34/1.29  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.29  tff(c_39, plain, (![A_25]: (k1_xboole_0=A_25 | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.29  tff(c_43, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_39])).
% 2.34/1.29  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.29  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.29  tff(c_37, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 2.34/1.29  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_37])).
% 2.34/1.29  tff(c_96, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.29  tff(c_99, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_96])).
% 2.34/1.29  tff(c_105, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_99])).
% 2.34/1.29  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.29  tff(c_44, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_2])).
% 2.34/1.29  tff(c_111, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_105, c_44])).
% 2.34/1.29  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.29  tff(c_58, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_12])).
% 2.34/1.29  tff(c_125, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_58])).
% 2.34/1.29  tff(c_61, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_43, c_10])).
% 2.34/1.29  tff(c_123, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_111, c_61])).
% 2.34/1.29  tff(c_178, plain, (![C_42, A_43, B_44]: (v1_partfun1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.34/1.29  tff(c_184, plain, (![C_42]: (v1_partfun1(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_178])).
% 2.34/1.29  tff(c_204, plain, (![C_52]: (v1_partfun1(C_52, '#skF_4') | ~m1_subset_1(C_52, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_184])).
% 2.34/1.29  tff(c_209, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_125, c_204])).
% 2.34/1.29  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.29  tff(c_231, plain, (![C_58, A_59, B_60]: (v1_funct_2(C_58, A_59, B_60) | ~v1_partfun1(C_58, A_59) | ~v1_funct_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.29  tff(c_241, plain, (![A_59, B_60]: (v1_funct_2('#skF_4', A_59, B_60) | ~v1_partfun1('#skF_4', A_59) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_125, c_231])).
% 2.34/1.29  tff(c_244, plain, (![A_59, B_60]: (v1_funct_2('#skF_4', A_59, B_60) | ~v1_partfun1('#skF_4', A_59))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_241])).
% 2.34/1.29  tff(c_195, plain, (![A_48, B_49, C_50, D_51]: (k8_relset_1(A_48, B_49, C_50, D_51)=k10_relat_1(C_50, D_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.34/1.29  tff(c_203, plain, (![A_48, B_49, D_51]: (k8_relset_1(A_48, B_49, '#skF_4', D_51)=k10_relat_1('#skF_4', D_51))), inference(resolution, [status(thm)], [c_125, c_195])).
% 2.34/1.29  tff(c_127, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_43])).
% 2.34/1.29  tff(c_26, plain, (![B_23, C_24]: (k8_relset_1(k1_xboole_0, B_23, C_24, B_23)=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))) | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.34/1.29  tff(c_38, plain, (![B_23, C_24]: (k8_relset_1(k1_xboole_0, B_23, C_24, B_23)=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~v1_funct_1(C_24))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 2.34/1.29  tff(c_308, plain, (![B_73, C_74]: (k8_relset_1('#skF_4', B_73, C_74, B_73)='#skF_4' | ~m1_subset_1(C_74, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(C_74, '#skF_4', B_73) | ~v1_funct_1(C_74))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_127, c_127, c_127, c_38])).
% 2.34/1.29  tff(c_311, plain, (![B_73]: (k8_relset_1('#skF_4', B_73, '#skF_4', B_73)='#skF_4' | ~v1_funct_2('#skF_4', '#skF_4', B_73) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_125, c_308])).
% 2.34/1.29  tff(c_325, plain, (![B_75]: (k10_relat_1('#skF_4', B_75)='#skF_4' | ~v1_funct_2('#skF_4', '#skF_4', B_75))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_203, c_311])).
% 2.34/1.29  tff(c_329, plain, (![B_60]: (k10_relat_1('#skF_4', B_60)='#skF_4' | ~v1_partfun1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_244, c_325])).
% 2.34/1.29  tff(c_335, plain, (![B_60]: (k10_relat_1('#skF_4', B_60)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_329])).
% 2.34/1.29  tff(c_28, plain, (![B_23, A_22, C_24]: (k1_xboole_0=B_23 | k8_relset_1(A_22, B_23, C_24, B_23)=A_22 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.34/1.29  tff(c_252, plain, (![B_65, A_66, C_67]: (B_65='#skF_4' | k8_relset_1(A_66, B_65, C_67, B_65)=A_66 | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))) | ~v1_funct_2(C_67, A_66, B_65) | ~v1_funct_1(C_67))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_28])).
% 2.34/1.29  tff(c_259, plain, (![B_65, A_66]: (B_65='#skF_4' | k8_relset_1(A_66, B_65, '#skF_4', B_65)=A_66 | ~v1_funct_2('#skF_4', A_66, B_65) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_125, c_252])).
% 2.34/1.29  tff(c_264, plain, (![B_68, A_69]: (B_68='#skF_4' | k10_relat_1('#skF_4', B_68)=A_69 | ~v1_funct_2('#skF_4', A_69, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_203, c_259])).
% 2.34/1.29  tff(c_278, plain, (![B_70, A_71]: (B_70='#skF_4' | k10_relat_1('#skF_4', B_70)=A_71 | ~v1_partfun1('#skF_4', A_71))), inference(resolution, [status(thm)], [c_244, c_264])).
% 2.34/1.29  tff(c_286, plain, (![B_72]: (B_72='#skF_4' | k10_relat_1('#skF_4', B_72)='#skF_4')), inference(resolution, [status(thm)], [c_209, c_278])).
% 2.34/1.29  tff(c_30, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.29  tff(c_77, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_43, c_30])).
% 2.34/1.29  tff(c_122, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_111, c_77])).
% 2.34/1.29  tff(c_221, plain, (k10_relat_1('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_122])).
% 2.34/1.29  tff(c_304, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_286, c_221])).
% 2.34/1.29  tff(c_315, plain, (k10_relat_1('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_221])).
% 2.34/1.29  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_335, c_315])).
% 2.34/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.29  
% 2.34/1.29  Inference rules
% 2.34/1.29  ----------------------
% 2.34/1.29  #Ref     : 0
% 2.34/1.29  #Sup     : 66
% 2.34/1.29  #Fact    : 0
% 2.34/1.29  #Define  : 0
% 2.34/1.29  #Split   : 1
% 2.34/1.29  #Chain   : 0
% 2.34/1.29  #Close   : 0
% 2.34/1.29  
% 2.34/1.29  Ordering : KBO
% 2.34/1.29  
% 2.34/1.29  Simplification rules
% 2.34/1.29  ----------------------
% 2.34/1.29  #Subsume      : 3
% 2.34/1.29  #Demod        : 60
% 2.34/1.29  #Tautology    : 46
% 2.34/1.29  #SimpNegUnit  : 0
% 2.34/1.29  #BackRed      : 18
% 2.34/1.29  
% 2.34/1.29  #Partial instantiations: 0
% 2.34/1.29  #Strategies tried      : 1
% 2.34/1.29  
% 2.34/1.29  Timing (in seconds)
% 2.34/1.29  ----------------------
% 2.34/1.29  Preprocessing        : 0.31
% 2.34/1.29  Parsing              : 0.16
% 2.34/1.29  CNF conversion       : 0.02
% 2.34/1.29  Main loop            : 0.21
% 2.34/1.29  Inferencing          : 0.07
% 2.34/1.29  Reduction            : 0.07
% 2.34/1.29  Demodulation         : 0.05
% 2.34/1.29  BG Simplification    : 0.01
% 2.34/1.29  Subsumption          : 0.03
% 2.34/1.29  Abstraction          : 0.01
% 2.34/1.29  MUC search           : 0.00
% 2.34/1.29  Cooper               : 0.00
% 2.34/1.29  Total                : 0.55
% 2.34/1.29  Index Insertion      : 0.00
% 2.34/1.29  Index Deletion       : 0.00
% 2.34/1.29  Index Matching       : 0.00
% 2.34/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
