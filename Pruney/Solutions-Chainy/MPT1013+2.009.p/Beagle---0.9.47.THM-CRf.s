%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:35 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   57 (  86 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 161 expanded)
%              Number of equality atoms :   31 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_52,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_35,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_35])).

tff(c_106,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k7_relset_1(A_40,B_41,C_42,D_43) = k9_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    ! [D_43] : k7_relset_1('#skF_1','#skF_1','#skF_2',D_43) = k9_relat_1('#skF_2',D_43) ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_146,plain,(
    ! [A_49,B_50,C_51] :
      ( k7_relset_1(A_49,B_50,C_51,A_49) = k2_relset_1(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_148,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_2','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_152,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_22,c_148])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_43,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_relset_1(A_33,B_34,C_35) = k2_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_54,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_50])).

tff(c_63,plain,(
    ! [B_36,A_37] :
      ( k9_relat_1(B_36,k2_relat_1(A_37)) = k2_relat_1(k5_relat_1(A_37,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [B_36] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_36)) = k9_relat_1(B_36,'#skF_1')
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_63])).

tff(c_79,plain,(
    ! [B_36] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_36)) = k9_relat_1(B_36,'#skF_1')
      | ~ v1_relat_1(B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_72])).

tff(c_187,plain,(
    ! [A_59,F_56,B_57,E_58,C_61,D_60] :
      ( k4_relset_1(A_59,B_57,C_61,D_60,E_58,F_56) = k5_relat_1(E_58,F_56)
      | ~ m1_subset_1(F_56,k1_zfmisc_1(k2_zfmisc_1(C_61,D_60)))
      | ~ m1_subset_1(E_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_194,plain,(
    ! [A_62,B_63,E_64] :
      ( k4_relset_1(A_62,B_63,'#skF_1','#skF_1',E_64,'#skF_2') = k5_relat_1(E_64,'#skF_2')
      | ~ m1_subset_1(E_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(resolution,[status(thm)],[c_26,c_187])).

tff(c_202,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_194])).

tff(c_229,plain,(
    ! [C_70,E_73,F_72,D_68,B_69,A_71] :
      ( m1_subset_1(k4_relset_1(A_71,B_69,C_70,D_68,E_73,F_72),k1_zfmisc_1(k2_zfmisc_1(A_71,D_68)))
      | ~ m1_subset_1(F_72,k1_zfmisc_1(k2_zfmisc_1(C_70,D_68)))
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_258,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_229])).

tff(c_275,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_258])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_relset_1(A_13,B_14,C_15) = k2_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_442,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_275,c_8])).

tff(c_18,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_207,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_18])).

tff(c_510,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_207])).

tff(c_517,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_510])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_152,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  %$ m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.69/1.39  
% 2.69/1.39  %Foreground sorts:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Background operators:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Foreground operators:
% 2.69/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.69/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.69/1.39  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.69/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.69/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.69/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.39  
% 2.69/1.40  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 2.69/1.40  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.40  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.69/1.40  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.69/1.40  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.69/1.40  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.69/1.40  tff(f_52, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.69/1.40  tff(f_42, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.69/1.40  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.40  tff(c_35, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.40  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_35])).
% 2.69/1.40  tff(c_106, plain, (![A_40, B_41, C_42, D_43]: (k7_relset_1(A_40, B_41, C_42, D_43)=k9_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.40  tff(c_111, plain, (![D_43]: (k7_relset_1('#skF_1', '#skF_1', '#skF_2', D_43)=k9_relat_1('#skF_2', D_43))), inference(resolution, [status(thm)], [c_26, c_106])).
% 2.69/1.40  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.40  tff(c_146, plain, (![A_49, B_50, C_51]: (k7_relset_1(A_49, B_50, C_51, A_49)=k2_relset_1(A_49, B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.40  tff(c_148, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_146])).
% 2.69/1.40  tff(c_152, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_22, c_148])).
% 2.69/1.40  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.40  tff(c_43, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.69/1.40  tff(c_20, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.40  tff(c_44, plain, (![A_33, B_34, C_35]: (k2_relset_1(A_33, B_34, C_35)=k2_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.40  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_44])).
% 2.69/1.40  tff(c_54, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_50])).
% 2.69/1.40  tff(c_63, plain, (![B_36, A_37]: (k9_relat_1(B_36, k2_relat_1(A_37))=k2_relat_1(k5_relat_1(A_37, B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.40  tff(c_72, plain, (![B_36]: (k2_relat_1(k5_relat_1('#skF_3', B_36))=k9_relat_1(B_36, '#skF_1') | ~v1_relat_1(B_36) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_63])).
% 2.69/1.40  tff(c_79, plain, (![B_36]: (k2_relat_1(k5_relat_1('#skF_3', B_36))=k9_relat_1(B_36, '#skF_1') | ~v1_relat_1(B_36))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_72])).
% 2.69/1.40  tff(c_187, plain, (![A_59, F_56, B_57, E_58, C_61, D_60]: (k4_relset_1(A_59, B_57, C_61, D_60, E_58, F_56)=k5_relat_1(E_58, F_56) | ~m1_subset_1(F_56, k1_zfmisc_1(k2_zfmisc_1(C_61, D_60))) | ~m1_subset_1(E_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_57))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.40  tff(c_194, plain, (![A_62, B_63, E_64]: (k4_relset_1(A_62, B_63, '#skF_1', '#skF_1', E_64, '#skF_2')=k5_relat_1(E_64, '#skF_2') | ~m1_subset_1(E_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(resolution, [status(thm)], [c_26, c_187])).
% 2.69/1.40  tff(c_202, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_194])).
% 2.69/1.40  tff(c_229, plain, (![C_70, E_73, F_72, D_68, B_69, A_71]: (m1_subset_1(k4_relset_1(A_71, B_69, C_70, D_68, E_73, F_72), k1_zfmisc_1(k2_zfmisc_1(A_71, D_68))) | ~m1_subset_1(F_72, k1_zfmisc_1(k2_zfmisc_1(C_70, D_68))) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_69))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.40  tff(c_258, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_202, c_229])).
% 2.69/1.40  tff(c_275, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_258])).
% 2.69/1.40  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_relset_1(A_13, B_14, C_15)=k2_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.40  tff(c_442, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_275, c_8])).
% 2.69/1.40  tff(c_18, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.40  tff(c_207, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_18])).
% 2.69/1.40  tff(c_510, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_207])).
% 2.69/1.40  tff(c_517, plain, (k9_relat_1('#skF_2', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_510])).
% 2.69/1.40  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_152, c_517])).
% 2.69/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  Inference rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Ref     : 0
% 2.69/1.40  #Sup     : 141
% 2.69/1.40  #Fact    : 0
% 2.69/1.40  #Define  : 0
% 2.69/1.40  #Split   : 0
% 2.69/1.40  #Chain   : 0
% 2.69/1.40  #Close   : 0
% 2.69/1.40  
% 2.69/1.40  Ordering : KBO
% 2.69/1.40  
% 2.69/1.40  Simplification rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Subsume      : 0
% 2.69/1.40  #Demod        : 28
% 2.69/1.40  #Tautology    : 50
% 2.69/1.40  #SimpNegUnit  : 0
% 2.69/1.40  #BackRed      : 2
% 2.69/1.40  
% 2.69/1.40  #Partial instantiations: 0
% 2.69/1.40  #Strategies tried      : 1
% 2.69/1.40  
% 2.69/1.40  Timing (in seconds)
% 2.69/1.40  ----------------------
% 2.69/1.41  Preprocessing        : 0.31
% 2.69/1.41  Parsing              : 0.17
% 2.69/1.41  CNF conversion       : 0.02
% 2.69/1.41  Main loop            : 0.31
% 2.69/1.41  Inferencing          : 0.12
% 2.69/1.41  Reduction            : 0.09
% 2.69/1.41  Demodulation         : 0.06
% 2.69/1.41  BG Simplification    : 0.02
% 2.69/1.41  Subsumption          : 0.06
% 2.69/1.41  Abstraction          : 0.02
% 2.69/1.41  MUC search           : 0.00
% 2.69/1.41  Cooper               : 0.00
% 2.69/1.41  Total                : 0.66
% 2.69/1.41  Index Insertion      : 0.00
% 2.69/1.41  Index Deletion       : 0.00
% 2.69/1.41  Index Matching       : 0.00
% 2.69/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
