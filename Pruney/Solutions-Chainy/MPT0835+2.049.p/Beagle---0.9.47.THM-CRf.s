%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:02 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 124 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 186 expanded)
%              Number of equality atoms :   43 (  98 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_8,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_132,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k7_relset_1(A_53,B_54,C_55,D_56) = k9_relat_1(C_55,D_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [D_56] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_56) = k9_relat_1('#skF_3',D_56) ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_60,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_relset_1(A_34,B_35,C_36) = k2_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_64,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_60])).

tff(c_209,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_relset_1(A_66,B_67,C_68,A_66) = k2_relset_1(A_66,B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_211,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_209])).

tff(c_213,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_64,c_211])).

tff(c_162,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k8_relset_1(A_58,B_59,C_60,D_61) = k10_relat_1(C_60,D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [D_61] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_61) = k10_relat_1('#skF_3',D_61) ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_6,plain,(
    ! [A_6] :
      ( k9_relat_1(A_6,k1_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k8_relset_1(A_42,B_43,C_44,D_45) = k10_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_89,plain,(
    ! [D_45] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_45) = k10_relat_1('#skF_3',D_45) ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_51,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_109,plain,(
    ! [A_50,B_51,C_52] :
      ( k8_relset_1(A_50,B_51,C_52,B_51) = k1_relset_1(A_50,B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_111,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_113,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_55,c_111])).

tff(c_72,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( k7_relset_1(A_37,B_38,C_39,D_40) = k9_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    ! [D_40] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_40) = k9_relat_1('#skF_3',D_40) ),
    inference(resolution,[status(thm)],[c_24,c_72])).

tff(c_22,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_22])).

tff(c_66,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_71,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66])).

tff(c_76,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_71])).

tff(c_90,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_76])).

tff(c_114,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_90])).

tff(c_121,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_114])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_121])).

tff(c_126,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_136,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_126])).

tff(c_168,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_136])).

tff(c_214,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_168])).

tff(c_221,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_214])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.23  
% 2.15/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.23  %$ m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.15/1.23  
% 2.15/1.23  %Foreground sorts:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Background operators:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Foreground operators:
% 2.15/1.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.15/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.23  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.15/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.15/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.15/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.15/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.23  
% 2.19/1.25  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.19/1.25  tff(f_71, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.19/1.25  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.19/1.25  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.19/1.25  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.19/1.25  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.19/1.25  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.19/1.25  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.19/1.25  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.19/1.25  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.19/1.25  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.25  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.25  tff(c_44, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.25  tff(c_47, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_44])).
% 2.19/1.25  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 2.19/1.25  tff(c_8, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.25  tff(c_132, plain, (![A_53, B_54, C_55, D_56]: (k7_relset_1(A_53, B_54, C_55, D_56)=k9_relat_1(C_55, D_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.25  tff(c_135, plain, (![D_56]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_56)=k9_relat_1('#skF_3', D_56))), inference(resolution, [status(thm)], [c_24, c_132])).
% 2.19/1.25  tff(c_60, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.25  tff(c_64, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_60])).
% 2.19/1.25  tff(c_209, plain, (![A_66, B_67, C_68]: (k7_relset_1(A_66, B_67, C_68, A_66)=k2_relset_1(A_66, B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.25  tff(c_211, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_209])).
% 2.19/1.25  tff(c_213, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_64, c_211])).
% 2.19/1.25  tff(c_162, plain, (![A_58, B_59, C_60, D_61]: (k8_relset_1(A_58, B_59, C_60, D_61)=k10_relat_1(C_60, D_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.25  tff(c_165, plain, (![D_61]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_61)=k10_relat_1('#skF_3', D_61))), inference(resolution, [status(thm)], [c_24, c_162])).
% 2.19/1.25  tff(c_6, plain, (![A_6]: (k9_relat_1(A_6, k1_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.19/1.25  tff(c_86, plain, (![A_42, B_43, C_44, D_45]: (k8_relset_1(A_42, B_43, C_44, D_45)=k10_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.25  tff(c_89, plain, (![D_45]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_45)=k10_relat_1('#skF_3', D_45))), inference(resolution, [status(thm)], [c_24, c_86])).
% 2.19/1.25  tff(c_51, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.25  tff(c_55, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_51])).
% 2.19/1.25  tff(c_109, plain, (![A_50, B_51, C_52]: (k8_relset_1(A_50, B_51, C_52, B_51)=k1_relset_1(A_50, B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.25  tff(c_111, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_109])).
% 2.19/1.25  tff(c_113, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_55, c_111])).
% 2.19/1.25  tff(c_72, plain, (![A_37, B_38, C_39, D_40]: (k7_relset_1(A_37, B_38, C_39, D_40)=k9_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.25  tff(c_75, plain, (![D_40]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_40)=k9_relat_1('#skF_3', D_40))), inference(resolution, [status(thm)], [c_24, c_72])).
% 2.19/1.25  tff(c_22, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.25  tff(c_65, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_22])).
% 2.19/1.25  tff(c_66, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_65])).
% 2.19/1.25  tff(c_71, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66])).
% 2.19/1.25  tff(c_76, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_71])).
% 2.19/1.25  tff(c_90, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_76])).
% 2.19/1.25  tff(c_114, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_90])).
% 2.19/1.25  tff(c_121, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_114])).
% 2.19/1.25  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_121])).
% 2.19/1.25  tff(c_126, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_65])).
% 2.19/1.25  tff(c_136, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_126])).
% 2.19/1.25  tff(c_168, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_136])).
% 2.19/1.25  tff(c_214, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_168])).
% 2.19/1.25  tff(c_221, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_214])).
% 2.19/1.25  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_221])).
% 2.19/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  Inference rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Ref     : 0
% 2.19/1.25  #Sup     : 51
% 2.19/1.25  #Fact    : 0
% 2.19/1.25  #Define  : 0
% 2.19/1.25  #Split   : 1
% 2.19/1.25  #Chain   : 0
% 2.19/1.25  #Close   : 0
% 2.19/1.25  
% 2.19/1.25  Ordering : KBO
% 2.19/1.25  
% 2.19/1.25  Simplification rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Subsume      : 0
% 2.19/1.25  #Demod        : 29
% 2.19/1.25  #Tautology    : 38
% 2.19/1.25  #SimpNegUnit  : 0
% 2.19/1.25  #BackRed      : 9
% 2.19/1.25  
% 2.19/1.25  #Partial instantiations: 0
% 2.19/1.25  #Strategies tried      : 1
% 2.19/1.25  
% 2.19/1.25  Timing (in seconds)
% 2.19/1.25  ----------------------
% 2.19/1.25  Preprocessing        : 0.31
% 2.19/1.25  Parsing              : 0.17
% 2.19/1.25  CNF conversion       : 0.02
% 2.19/1.25  Main loop            : 0.17
% 2.19/1.25  Inferencing          : 0.07
% 2.19/1.25  Reduction            : 0.06
% 2.19/1.25  Demodulation         : 0.04
% 2.19/1.25  BG Simplification    : 0.01
% 2.19/1.25  Subsumption          : 0.02
% 2.19/1.25  Abstraction          : 0.01
% 2.19/1.25  MUC search           : 0.00
% 2.19/1.25  Cooper               : 0.00
% 2.19/1.25  Total                : 0.52
% 2.19/1.25  Index Insertion      : 0.00
% 2.19/1.25  Index Deletion       : 0.00
% 2.19/1.25  Index Matching       : 0.00
% 2.19/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
