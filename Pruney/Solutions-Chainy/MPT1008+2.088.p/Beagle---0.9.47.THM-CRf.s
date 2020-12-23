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
% DateTime   : Thu Dec  3 10:14:38 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 104 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 190 expanded)
%              Number of equality atoms :   43 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_94,plain,(
    ! [B_46,A_47] :
      ( k1_tarski(k1_funct_1(B_46,A_47)) = k2_relat_1(B_46)
      | k1_tarski(A_47) != k1_relat_1(B_46)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_80])).

tff(c_30,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_85,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_30])).

tff(c_100,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_85])).

tff(c_107,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_38,c_100])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_90,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k8_relset_1(A_42,B_43,C_44,D_45) = k10_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    ! [D_45] : k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_45) = k10_relat_1('#skF_3',D_45) ),
    inference(resolution,[status(thm)],[c_34,c_90])).

tff(c_127,plain,(
    ! [A_52,B_53,C_54] :
      ( k7_relset_1(A_52,B_53,C_54,A_52) = k2_relset_1(A_52,B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_129,plain,(
    k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1')) = k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_127])).

tff(c_131,plain,(
    k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_129])).

tff(c_118,plain,(
    ! [A_49,B_50,C_51] :
      ( k8_relset_1(A_49,B_50,C_51,B_50) = k1_relset_1(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_120,plain,(
    k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3','#skF_2') = k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_122,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_120])).

tff(c_137,plain,(
    ! [B_57,A_58,C_59] :
      ( k8_relset_1(B_57,A_58,C_59,k7_relset_1(B_57,A_58,C_59,B_57)) = k1_relset_1(B_57,A_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(B_57,A_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_139,plain,(
    k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1'))) = k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_141,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_131,c_122,c_139])).

tff(c_8,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_152,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_145])).

tff(c_193,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k8_relset_1(A_64,B_63,C_65,B_63) = A_64
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63)))
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ v1_funct_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_195,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3','#skF_2') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_193])).

tff(c_198,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_152,c_93,c_195])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_32,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.21  
% 2.11/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.22  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.22  
% 2.11/1.22  %Foreground sorts:
% 2.11/1.22  
% 2.11/1.22  
% 2.11/1.22  %Background operators:
% 2.11/1.22  
% 2.11/1.22  
% 2.11/1.22  %Foreground operators:
% 2.11/1.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.11/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.22  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.11/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.22  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.11/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.11/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.11/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.22  
% 2.11/1.23  tff(f_91, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.11/1.23  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.11/1.23  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.11/1.23  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.11/1.23  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.11/1.23  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.11/1.23  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.11/1.23  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.11/1.23  tff(f_79, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 2.11/1.23  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.11/1.23  tff(c_57, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.23  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_57])).
% 2.11/1.23  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.11/1.23  tff(c_94, plain, (![B_46, A_47]: (k1_tarski(k1_funct_1(B_46, A_47))=k2_relat_1(B_46) | k1_tarski(A_47)!=k1_relat_1(B_46) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.23  tff(c_80, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.23  tff(c_84, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_80])).
% 2.11/1.23  tff(c_30, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.11/1.23  tff(c_85, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_30])).
% 2.11/1.23  tff(c_100, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_94, c_85])).
% 2.11/1.23  tff(c_107, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_38, c_100])).
% 2.11/1.23  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.11/1.23  tff(c_36, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.11/1.23  tff(c_90, plain, (![A_42, B_43, C_44, D_45]: (k8_relset_1(A_42, B_43, C_44, D_45)=k10_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.23  tff(c_93, plain, (![D_45]: (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_45)=k10_relat_1('#skF_3', D_45))), inference(resolution, [status(thm)], [c_34, c_90])).
% 2.11/1.23  tff(c_127, plain, (![A_52, B_53, C_54]: (k7_relset_1(A_52, B_53, C_54, A_52)=k2_relset_1(A_52, B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.11/1.23  tff(c_129, plain, (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1'))=k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_127])).
% 2.11/1.23  tff(c_131, plain, (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_129])).
% 2.11/1.23  tff(c_118, plain, (![A_49, B_50, C_51]: (k8_relset_1(A_49, B_50, C_51, B_50)=k1_relset_1(A_49, B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.11/1.23  tff(c_120, plain, (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', '#skF_2')=k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_118])).
% 2.11/1.23  tff(c_122, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_120])).
% 2.11/1.23  tff(c_137, plain, (![B_57, A_58, C_59]: (k8_relset_1(B_57, A_58, C_59, k7_relset_1(B_57, A_58, C_59, B_57))=k1_relset_1(B_57, A_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(B_57, A_58))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.11/1.23  tff(c_139, plain, (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1')))=k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_137])).
% 2.11/1.23  tff(c_141, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_131, c_122, c_139])).
% 2.11/1.23  tff(c_8, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.23  tff(c_145, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 2.11/1.23  tff(c_152, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_145])).
% 2.11/1.23  tff(c_193, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k8_relset_1(A_64, B_63, C_65, B_63)=A_64 | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))) | ~v1_funct_2(C_65, A_64, B_63) | ~v1_funct_1(C_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.23  tff(c_195, plain, (k1_xboole_0='#skF_2' | k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', '#skF_2')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_193])).
% 2.11/1.23  tff(c_198, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_152, c_93, c_195])).
% 2.11/1.23  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_32, c_198])).
% 2.11/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  Inference rules
% 2.11/1.23  ----------------------
% 2.11/1.23  #Ref     : 0
% 2.11/1.23  #Sup     : 41
% 2.11/1.23  #Fact    : 0
% 2.11/1.23  #Define  : 0
% 2.11/1.23  #Split   : 0
% 2.11/1.23  #Chain   : 0
% 2.11/1.23  #Close   : 0
% 2.11/1.23  
% 2.11/1.23  Ordering : KBO
% 2.11/1.23  
% 2.11/1.23  Simplification rules
% 2.11/1.23  ----------------------
% 2.11/1.23  #Subsume      : 0
% 2.11/1.23  #Demod        : 22
% 2.11/1.23  #Tautology    : 31
% 2.11/1.23  #SimpNegUnit  : 1
% 2.11/1.23  #BackRed      : 3
% 2.11/1.23  
% 2.11/1.23  #Partial instantiations: 0
% 2.11/1.23  #Strategies tried      : 1
% 2.11/1.23  
% 2.11/1.23  Timing (in seconds)
% 2.11/1.23  ----------------------
% 2.19/1.23  Preprocessing        : 0.33
% 2.19/1.23  Parsing              : 0.18
% 2.19/1.23  CNF conversion       : 0.02
% 2.19/1.23  Main loop            : 0.15
% 2.19/1.23  Inferencing          : 0.06
% 2.19/1.23  Reduction            : 0.05
% 2.19/1.24  Demodulation         : 0.04
% 2.19/1.24  BG Simplification    : 0.01
% 2.19/1.24  Subsumption          : 0.02
% 2.19/1.24  Abstraction          : 0.01
% 2.19/1.24  MUC search           : 0.00
% 2.19/1.24  Cooper               : 0.00
% 2.19/1.24  Total                : 0.51
% 2.19/1.24  Index Insertion      : 0.00
% 2.19/1.24  Index Deletion       : 0.00
% 2.19/1.24  Index Matching       : 0.00
% 2.19/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
