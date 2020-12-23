%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:59 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 122 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 182 expanded)
%              Number of equality atoms :   42 ( 102 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_4,plain,(
    ! [A_2] :
      ( k10_relat_1(A_2,k2_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k7_relset_1(A_55,B_56,C_57,D_58) = k9_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_155,plain,(
    ! [D_58] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_58) = k9_relat_1('#skF_3',D_58) ),
    inference(resolution,[status(thm)],[c_22,c_152])).

tff(c_55,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_177,plain,(
    ! [A_60,B_61,C_62] :
      ( k7_relset_1(A_60,B_61,C_62,A_60) = k2_relset_1(A_60,B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_181,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_59,c_179])).

tff(c_133,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k8_relset_1(A_50,B_51,C_52,D_53) = k10_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    ! [D_53] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_53) = k10_relat_1('#skF_3',D_53) ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k8_relset_1(A_34,B_35,C_36,D_37) = k10_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    ! [D_37] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_37) = k10_relat_1('#skF_3',D_37) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_46,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_114,plain,(
    ! [A_47,B_48,C_49] :
      ( k8_relset_1(A_47,B_48,C_49,B_48) = k1_relset_1(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_114])).

tff(c_118,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_50,c_116])).

tff(c_80,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k7_relset_1(A_39,B_40,C_41,D_42) = k9_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [D_42] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_42) = k9_relat_1('#skF_3',D_42) ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_20,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_50,c_20])).

tff(c_65,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_65])).

tff(c_93,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_70])).

tff(c_119,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_93])).

tff(c_126,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_126])).

tff(c_131,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_137,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_131])).

tff(c_156,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_137])).

tff(c_187,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_156])).

tff(c_200,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_187])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.18  
% 1.93/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.18  %$ m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.18  
% 1.93/1.18  %Foreground sorts:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Background operators:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Foreground operators:
% 1.93/1.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.93/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.18  
% 1.93/1.20  tff(f_66, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 1.93/1.20  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/1.20  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.93/1.20  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.93/1.20  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.93/1.20  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 1.93/1.20  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.93/1.20  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.93/1.20  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.93/1.20  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.20  tff(c_32, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.20  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_32])).
% 1.93/1.20  tff(c_4, plain, (![A_2]: (k10_relat_1(A_2, k2_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.20  tff(c_152, plain, (![A_55, B_56, C_57, D_58]: (k7_relset_1(A_55, B_56, C_57, D_58)=k9_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.20  tff(c_155, plain, (![D_58]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_58)=k9_relat_1('#skF_3', D_58))), inference(resolution, [status(thm)], [c_22, c_152])).
% 1.93/1.20  tff(c_55, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.20  tff(c_59, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_55])).
% 1.93/1.20  tff(c_177, plain, (![A_60, B_61, C_62]: (k7_relset_1(A_60, B_61, C_62, A_60)=k2_relset_1(A_60, B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.20  tff(c_179, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_177])).
% 1.93/1.20  tff(c_181, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_59, c_179])).
% 1.93/1.20  tff(c_133, plain, (![A_50, B_51, C_52, D_53]: (k8_relset_1(A_50, B_51, C_52, D_53)=k10_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.20  tff(c_136, plain, (![D_53]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_53)=k10_relat_1('#skF_3', D_53))), inference(resolution, [status(thm)], [c_22, c_133])).
% 1.93/1.20  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.20  tff(c_66, plain, (![A_34, B_35, C_36, D_37]: (k8_relset_1(A_34, B_35, C_36, D_37)=k10_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.20  tff(c_69, plain, (![D_37]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_37)=k10_relat_1('#skF_3', D_37))), inference(resolution, [status(thm)], [c_22, c_66])).
% 1.93/1.20  tff(c_46, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.20  tff(c_50, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_46])).
% 1.93/1.20  tff(c_114, plain, (![A_47, B_48, C_49]: (k8_relset_1(A_47, B_48, C_49, B_48)=k1_relset_1(A_47, B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.20  tff(c_116, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_114])).
% 1.93/1.20  tff(c_118, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_50, c_116])).
% 1.93/1.20  tff(c_80, plain, (![A_39, B_40, C_41, D_42]: (k7_relset_1(A_39, B_40, C_41, D_42)=k9_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.20  tff(c_83, plain, (![D_42]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_42)=k9_relat_1('#skF_3', D_42))), inference(resolution, [status(thm)], [c_22, c_80])).
% 1.93/1.20  tff(c_20, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.20  tff(c_64, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_50, c_20])).
% 1.93/1.20  tff(c_65, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 1.93/1.20  tff(c_70, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_65])).
% 1.93/1.20  tff(c_93, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_70])).
% 1.93/1.20  tff(c_119, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_93])).
% 1.93/1.20  tff(c_126, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 1.93/1.20  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_126])).
% 1.93/1.20  tff(c_131, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 1.93/1.20  tff(c_137, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_131])).
% 1.93/1.20  tff(c_156, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_137])).
% 1.93/1.20  tff(c_187, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_156])).
% 1.93/1.20  tff(c_200, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_187])).
% 1.93/1.20  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_200])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 47
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 1
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 0
% 1.93/1.20  #Demod        : 22
% 1.93/1.20  #Tautology    : 32
% 1.93/1.20  #SimpNegUnit  : 0
% 1.93/1.20  #BackRed      : 8
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.29
% 1.93/1.20  Parsing              : 0.16
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.15
% 1.93/1.20  Inferencing          : 0.06
% 1.93/1.20  Reduction            : 0.05
% 1.93/1.20  Demodulation         : 0.04
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.01
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.20  MUC search           : 0.00
% 1.93/1.20  Cooper               : 0.00
% 1.93/1.20  Total                : 0.47
% 1.93/1.20  Index Insertion      : 0.00
% 1.93/1.20  Index Deletion       : 0.00
% 1.93/1.20  Index Matching       : 0.00
% 1.93/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
