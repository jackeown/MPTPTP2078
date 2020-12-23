%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:35 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 108 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 219 expanded)
%              Number of equality atoms :   31 ( 101 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_41,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_42,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k7_relset_1(A_31,B_32,C_33,D_34) = k9_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    ! [D_34] : k7_relset_1('#skF_1','#skF_1','#skF_2',D_34) = k9_relat_1('#skF_2',D_34) ),
    inference(resolution,[status(thm)],[c_24,c_42])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,(
    ! [A_43,B_44,C_45] :
      ( k7_relset_1(A_43,B_44,C_45,A_43) = k2_relset_1(A_43,B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_2','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_97,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_20,c_93])).

tff(c_48,plain,(
    ! [D_34] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_34) = k9_relat_1('#skF_3',D_34) ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_18,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_95,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_91])).

tff(c_99,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18,c_95])).

tff(c_2,plain,(
    ! [B_2,C_4,A_1] :
      ( k9_relat_1(k5_relat_1(B_2,C_4),A_1) = k9_relat_1(C_4,k9_relat_1(B_2,A_1))
      | ~ v1_relat_1(C_4)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [D_48,B_50,E_46,A_51,C_49,F_47] :
      ( k4_relset_1(A_51,B_50,C_49,D_48,E_46,F_47) = k5_relat_1(E_46,F_47)
      | ~ m1_subset_1(F_47,k1_zfmisc_1(k2_zfmisc_1(C_49,D_48)))
      | ~ m1_subset_1(E_46,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [A_52,B_53,E_54] :
      ( k4_relset_1(A_52,B_53,'#skF_1','#skF_1',E_54,'#skF_2') = k5_relat_1(E_54,'#skF_2')
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(resolution,[status(thm)],[c_24,c_108])).

tff(c_123,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_146,plain,(
    ! [D_63,C_62,A_59,B_61,E_60,F_58] :
      ( m1_subset_1(k4_relset_1(A_59,B_61,C_62,D_63,E_60,F_58),k1_zfmisc_1(k2_zfmisc_1(A_59,D_63)))
      | ~ m1_subset_1(F_58,k1_zfmisc_1(k2_zfmisc_1(C_62,D_63)))
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(A_59,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_169,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_146])).

tff(c_183,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_169])).

tff(c_10,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k7_relset_1(A_20,B_21,C_22,D_23) = k9_relat_1(C_22,D_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_232,plain,(
    ! [D_23] : k7_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2'),D_23) = k9_relat_1(k5_relat_1('#skF_3','#skF_2'),D_23) ),
    inference(resolution,[status(thm)],[c_183,c_10])).

tff(c_14,plain,(
    ! [A_24,B_25,C_26] :
      ( k7_relset_1(A_24,B_25,C_26,A_24) = k2_relset_1(A_24,B_25,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_230,plain,(
    k7_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2'),'#skF_1') = k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_183,c_14])).

tff(c_448,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k9_relat_1(k5_relat_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_230])).

tff(c_16,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_16])).

tff(c_449,plain,(
    k9_relat_1(k5_relat_1('#skF_3','#skF_2'),'#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_128])).

tff(c_478,plain,
    ( k9_relat_1('#skF_2',k9_relat_1('#skF_3','#skF_1')) != '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_449])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_40,c_97,c_99,c_478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.44  
% 2.59/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.44  %$ m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.59/1.44  
% 2.59/1.44  %Foreground sorts:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Background operators:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Foreground operators:
% 2.59/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.59/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.59/1.44  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.59/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.59/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.59/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.44  
% 2.59/1.45  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 2.59/1.45  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.59/1.45  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.59/1.45  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.59/1.45  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.59/1.45  tff(f_48, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.59/1.45  tff(f_42, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.59/1.45  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.45  tff(c_33, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.59/1.45  tff(c_41, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_33])).
% 2.59/1.45  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.45  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_33])).
% 2.59/1.45  tff(c_42, plain, (![A_31, B_32, C_33, D_34]: (k7_relset_1(A_31, B_32, C_33, D_34)=k9_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.59/1.45  tff(c_47, plain, (![D_34]: (k7_relset_1('#skF_1', '#skF_1', '#skF_2', D_34)=k9_relat_1('#skF_2', D_34))), inference(resolution, [status(thm)], [c_24, c_42])).
% 2.59/1.45  tff(c_20, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.45  tff(c_91, plain, (![A_43, B_44, C_45]: (k7_relset_1(A_43, B_44, C_45, A_43)=k2_relset_1(A_43, B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.59/1.45  tff(c_93, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_91])).
% 2.59/1.45  tff(c_97, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_20, c_93])).
% 2.59/1.45  tff(c_48, plain, (![D_34]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_34)=k9_relat_1('#skF_3', D_34))), inference(resolution, [status(thm)], [c_22, c_42])).
% 2.59/1.45  tff(c_18, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.45  tff(c_95, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_91])).
% 2.59/1.45  tff(c_99, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18, c_95])).
% 2.59/1.45  tff(c_2, plain, (![B_2, C_4, A_1]: (k9_relat_1(k5_relat_1(B_2, C_4), A_1)=k9_relat_1(C_4, k9_relat_1(B_2, A_1)) | ~v1_relat_1(C_4) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.45  tff(c_108, plain, (![D_48, B_50, E_46, A_51, C_49, F_47]: (k4_relset_1(A_51, B_50, C_49, D_48, E_46, F_47)=k5_relat_1(E_46, F_47) | ~m1_subset_1(F_47, k1_zfmisc_1(k2_zfmisc_1(C_49, D_48))) | ~m1_subset_1(E_46, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.45  tff(c_115, plain, (![A_52, B_53, E_54]: (k4_relset_1(A_52, B_53, '#skF_1', '#skF_1', E_54, '#skF_2')=k5_relat_1(E_54, '#skF_2') | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(resolution, [status(thm)], [c_24, c_108])).
% 2.59/1.45  tff(c_123, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_115])).
% 2.59/1.45  tff(c_146, plain, (![D_63, C_62, A_59, B_61, E_60, F_58]: (m1_subset_1(k4_relset_1(A_59, B_61, C_62, D_63, E_60, F_58), k1_zfmisc_1(k2_zfmisc_1(A_59, D_63))) | ~m1_subset_1(F_58, k1_zfmisc_1(k2_zfmisc_1(C_62, D_63))) | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(A_59, B_61))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.45  tff(c_169, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_146])).
% 2.59/1.45  tff(c_183, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_169])).
% 2.59/1.45  tff(c_10, plain, (![A_20, B_21, C_22, D_23]: (k7_relset_1(A_20, B_21, C_22, D_23)=k9_relat_1(C_22, D_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.59/1.45  tff(c_232, plain, (![D_23]: (k7_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'), D_23)=k9_relat_1(k5_relat_1('#skF_3', '#skF_2'), D_23))), inference(resolution, [status(thm)], [c_183, c_10])).
% 2.59/1.45  tff(c_14, plain, (![A_24, B_25, C_26]: (k7_relset_1(A_24, B_25, C_26, A_24)=k2_relset_1(A_24, B_25, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.59/1.45  tff(c_230, plain, (k7_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'), '#skF_1')=k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_183, c_14])).
% 2.59/1.45  tff(c_448, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k9_relat_1(k5_relat_1('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_230])).
% 2.59/1.45  tff(c_16, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.45  tff(c_128, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_16])).
% 2.59/1.45  tff(c_449, plain, (k9_relat_1(k5_relat_1('#skF_3', '#skF_2'), '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_448, c_128])).
% 2.59/1.45  tff(c_478, plain, (k9_relat_1('#skF_2', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_449])).
% 2.59/1.45  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_40, c_97, c_99, c_478])).
% 2.59/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.45  
% 2.59/1.45  Inference rules
% 2.59/1.45  ----------------------
% 2.59/1.45  #Ref     : 0
% 2.59/1.45  #Sup     : 131
% 2.59/1.45  #Fact    : 0
% 2.59/1.45  #Define  : 0
% 2.59/1.45  #Split   : 0
% 2.59/1.45  #Chain   : 0
% 2.59/1.45  #Close   : 0
% 2.59/1.45  
% 2.59/1.45  Ordering : KBO
% 2.59/1.45  
% 2.59/1.45  Simplification rules
% 2.59/1.45  ----------------------
% 2.59/1.45  #Subsume      : 0
% 2.59/1.45  #Demod        : 30
% 2.59/1.45  #Tautology    : 46
% 2.59/1.45  #SimpNegUnit  : 0
% 2.59/1.45  #BackRed      : 2
% 2.59/1.45  
% 2.59/1.45  #Partial instantiations: 0
% 2.59/1.45  #Strategies tried      : 1
% 2.59/1.45  
% 2.59/1.45  Timing (in seconds)
% 2.59/1.45  ----------------------
% 2.59/1.46  Preprocessing        : 0.33
% 2.59/1.46  Parsing              : 0.18
% 2.59/1.46  CNF conversion       : 0.02
% 2.59/1.46  Main loop            : 0.32
% 2.59/1.46  Inferencing          : 0.12
% 2.59/1.46  Reduction            : 0.09
% 2.59/1.46  Demodulation         : 0.07
% 2.59/1.46  BG Simplification    : 0.02
% 2.59/1.46  Subsumption          : 0.06
% 2.59/1.46  Abstraction          : 0.02
% 2.59/1.46  MUC search           : 0.00
% 2.59/1.46  Cooper               : 0.00
% 2.59/1.46  Total                : 0.68
% 2.59/1.46  Index Insertion      : 0.00
% 2.59/1.46  Index Deletion       : 0.00
% 2.59/1.46  Index Matching       : 0.00
% 2.59/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
