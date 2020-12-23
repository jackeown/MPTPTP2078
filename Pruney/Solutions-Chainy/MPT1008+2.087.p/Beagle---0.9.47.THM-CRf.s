%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:38 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   60 (  97 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 194 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_31,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,(
    ! [B_36,A_37] :
      ( k1_tarski(k1_funct_1(B_36,A_37)) = k2_relat_1(B_36)
      | k1_tarski(A_37) != k1_relat_1(B_36)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_22,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_22])).

tff(c_74,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_50])).

tff(c_81,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_30,c_74])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k7_relset_1(A_38,B_39,C_40,D_41) = k9_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [D_41] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_41) = k9_relat_1('#skF_3',D_41) ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_98,plain,(
    ! [B_47,A_48,C_49] :
      ( k1_xboole_0 = B_47
      | k7_relset_1(A_48,B_47,C_49,A_48) = k2_relset_1(A_48,B_47,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47)))
      | ~ v1_funct_2(C_49,A_48,B_47)
      | ~ v1_funct_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,
    ( k1_xboole_0 = '#skF_2'
    | k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1')) = k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_103,plain,
    ( k1_xboole_0 = '#skF_2'
    | k9_relat_1('#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_86,c_49,c_100])).

tff(c_104,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_103])).

tff(c_55,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k8_relset_1(A_31,B_32,C_33,D_34) = k10_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    ! [D_34] : k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_34) = k10_relat_1('#skF_3',D_34) ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_109,plain,(
    ! [B_50,A_51,C_52] :
      ( k1_xboole_0 = B_50
      | k8_relset_1(A_51,B_50,C_52,k7_relset_1(A_51,B_50,C_52,A_51)) = A_51
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50)))
      | ~ v1_funct_2(C_52,A_51,B_50)
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_111,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1'))) = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_109])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_104,c_86,c_58,c_111])).

tff(c_115,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_114])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_126,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_119])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.93/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.21  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.21  
% 1.93/1.22  tff(f_89, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 1.93/1.22  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/1.22  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 1.93/1.22  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.93/1.22  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.93/1.22  tff(f_65, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_funct_2)).
% 1.93/1.22  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.93/1.22  tff(f_77, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 1.93/1.22  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.93/1.22  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.22  tff(c_31, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.22  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_31])).
% 1.93/1.22  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.22  tff(c_68, plain, (![B_36, A_37]: (k1_tarski(k1_funct_1(B_36, A_37))=k2_relat_1(B_36) | k1_tarski(A_37)!=k1_relat_1(B_36) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.22  tff(c_45, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.22  tff(c_49, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_45])).
% 1.93/1.22  tff(c_22, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.22  tff(c_50, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_22])).
% 1.93/1.22  tff(c_74, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_68, c_50])).
% 1.93/1.22  tff(c_81, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_30, c_74])).
% 1.93/1.22  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.22  tff(c_28, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.22  tff(c_83, plain, (![A_38, B_39, C_40, D_41]: (k7_relset_1(A_38, B_39, C_40, D_41)=k9_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.22  tff(c_86, plain, (![D_41]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_41)=k9_relat_1('#skF_3', D_41))), inference(resolution, [status(thm)], [c_26, c_83])).
% 1.93/1.22  tff(c_98, plain, (![B_47, A_48, C_49]: (k1_xboole_0=B_47 | k7_relset_1(A_48, B_47, C_49, A_48)=k2_relset_1(A_48, B_47, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))) | ~v1_funct_2(C_49, A_48, B_47) | ~v1_funct_1(C_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.22  tff(c_100, plain, (k1_xboole_0='#skF_2' | k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1'))=k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_98])).
% 1.93/1.22  tff(c_103, plain, (k1_xboole_0='#skF_2' | k9_relat_1('#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_86, c_49, c_100])).
% 1.93/1.22  tff(c_104, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_24, c_103])).
% 1.93/1.22  tff(c_55, plain, (![A_31, B_32, C_33, D_34]: (k8_relset_1(A_31, B_32, C_33, D_34)=k10_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.22  tff(c_58, plain, (![D_34]: (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_34)=k10_relat_1('#skF_3', D_34))), inference(resolution, [status(thm)], [c_26, c_55])).
% 1.93/1.22  tff(c_109, plain, (![B_50, A_51, C_52]: (k1_xboole_0=B_50 | k8_relset_1(A_51, B_50, C_52, k7_relset_1(A_51, B_50, C_52, A_51))=A_51 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))) | ~v1_funct_2(C_52, A_51, B_50) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.93/1.22  tff(c_111, plain, (k1_xboole_0='#skF_2' | k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1')))=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_109])).
% 1.93/1.22  tff(c_114, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_104, c_86, c_58, c_111])).
% 1.93/1.22  tff(c_115, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_114])).
% 1.93/1.22  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.22  tff(c_119, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 1.93/1.22  tff(c_126, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_119])).
% 1.93/1.22  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_126])).
% 1.93/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  Inference rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 23
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 0
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 0
% 1.93/1.22  #Demod        : 13
% 1.93/1.22  #Tautology    : 13
% 1.93/1.22  #SimpNegUnit  : 3
% 1.93/1.22  #BackRed      : 1
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.22  Preprocessing        : 0.31
% 1.93/1.22  Parsing              : 0.17
% 1.93/1.22  CNF conversion       : 0.02
% 1.93/1.22  Main loop            : 0.13
% 1.93/1.22  Inferencing          : 0.05
% 1.93/1.22  Reduction            : 0.04
% 1.93/1.22  Demodulation         : 0.03
% 1.93/1.22  BG Simplification    : 0.01
% 1.93/1.22  Subsumption          : 0.01
% 1.93/1.22  Abstraction          : 0.01
% 1.93/1.22  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.47
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
