%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:36 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   61 (  92 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 173 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_47,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_113,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k7_relset_1(A_43,B_44,C_45,D_46) = k9_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [D_46] : k7_relset_1('#skF_1','#skF_1','#skF_2',D_46) = k9_relat_1('#skF_2',D_46) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_138,plain,(
    ! [A_49,B_50,C_51] :
      ( k7_relset_1(A_49,B_50,C_51,A_49) = k2_relset_1(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_140,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_2','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_138])).

tff(c_144,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_24,c_140])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_44])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_relset_1(A_38,B_39,C_40) = k2_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_70,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( k9_relat_1(B_8,k2_relat_1(A_6)) = k2_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [B_8] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_8)) = k9_relat_1(B_8,'#skF_1')
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_87,plain,(
    ! [B_8] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_8)) = k9_relat_1(B_8,'#skF_1')
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83])).

tff(c_182,plain,(
    ! [A_57,B_62,E_59,D_61,C_58,F_60] :
      ( k4_relset_1(A_57,B_62,C_58,D_61,E_59,F_60) = k5_relat_1(E_59,F_60)
      | ~ m1_subset_1(F_60,k1_zfmisc_1(k2_zfmisc_1(C_58,D_61)))
      | ~ m1_subset_1(E_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,(
    ! [A_63,B_64,E_65] :
      ( k4_relset_1(A_63,B_64,'#skF_1','#skF_1',E_65,'#skF_2') = k5_relat_1(E_65,'#skF_2')
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(resolution,[status(thm)],[c_28,c_182])).

tff(c_197,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_189])).

tff(c_236,plain,(
    ! [D_74,A_76,C_73,F_71,B_72,E_75] :
      ( m1_subset_1(k4_relset_1(A_76,B_72,C_73,D_74,E_75,F_71),k1_zfmisc_1(k2_zfmisc_1(A_76,D_74)))
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(C_73,D_74)))
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_265,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_236])).

tff(c_284,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_265])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_419,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_284,c_10])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_202,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_20])).

tff(c_517,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_202])).

tff(c_524,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_517])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_144,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.43  
% 2.54/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.44  %$ m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.54/1.44  
% 2.54/1.44  %Foreground sorts:
% 2.54/1.44  
% 2.54/1.44  
% 2.54/1.44  %Background operators:
% 2.54/1.44  
% 2.54/1.44  
% 2.54/1.44  %Foreground operators:
% 2.54/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.54/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.54/1.44  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.54/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.54/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.44  
% 2.88/1.45  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.88/1.45  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_2)).
% 2.88/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.88/1.45  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.88/1.45  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.88/1.45  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.88/1.45  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.88/1.45  tff(f_57, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.88/1.45  tff(f_47, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.88/1.45  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.88/1.45  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.45  tff(c_38, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.45  tff(c_41, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_38])).
% 2.88/1.45  tff(c_47, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_41])).
% 2.88/1.45  tff(c_113, plain, (![A_43, B_44, C_45, D_46]: (k7_relset_1(A_43, B_44, C_45, D_46)=k9_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.45  tff(c_118, plain, (![D_46]: (k7_relset_1('#skF_1', '#skF_1', '#skF_2', D_46)=k9_relat_1('#skF_2', D_46))), inference(resolution, [status(thm)], [c_28, c_113])).
% 2.88/1.45  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.45  tff(c_138, plain, (![A_49, B_50, C_51]: (k7_relset_1(A_49, B_50, C_51, A_49)=k2_relset_1(A_49, B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.45  tff(c_140, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_138])).
% 2.88/1.45  tff(c_144, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_24, c_140])).
% 2.88/1.45  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.45  tff(c_44, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_38])).
% 2.88/1.45  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_44])).
% 2.88/1.45  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.45  tff(c_60, plain, (![A_38, B_39, C_40]: (k2_relset_1(A_38, B_39, C_40)=k2_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.45  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_60])).
% 2.88/1.45  tff(c_70, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_66])).
% 2.88/1.45  tff(c_6, plain, (![B_8, A_6]: (k9_relat_1(B_8, k2_relat_1(A_6))=k2_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.45  tff(c_83, plain, (![B_8]: (k2_relat_1(k5_relat_1('#skF_3', B_8))=k9_relat_1(B_8, '#skF_1') | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 2.88/1.45  tff(c_87, plain, (![B_8]: (k2_relat_1(k5_relat_1('#skF_3', B_8))=k9_relat_1(B_8, '#skF_1') | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83])).
% 2.88/1.45  tff(c_182, plain, (![A_57, B_62, E_59, D_61, C_58, F_60]: (k4_relset_1(A_57, B_62, C_58, D_61, E_59, F_60)=k5_relat_1(E_59, F_60) | ~m1_subset_1(F_60, k1_zfmisc_1(k2_zfmisc_1(C_58, D_61))) | ~m1_subset_1(E_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_62))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.88/1.45  tff(c_189, plain, (![A_63, B_64, E_65]: (k4_relset_1(A_63, B_64, '#skF_1', '#skF_1', E_65, '#skF_2')=k5_relat_1(E_65, '#skF_2') | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(resolution, [status(thm)], [c_28, c_182])).
% 2.88/1.45  tff(c_197, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_189])).
% 2.88/1.45  tff(c_236, plain, (![D_74, A_76, C_73, F_71, B_72, E_75]: (m1_subset_1(k4_relset_1(A_76, B_72, C_73, D_74, E_75, F_71), k1_zfmisc_1(k2_zfmisc_1(A_76, D_74))) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(C_73, D_74))) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_72))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.45  tff(c_265, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_236])).
% 2.88/1.45  tff(c_284, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_265])).
% 2.88/1.45  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.45  tff(c_419, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_284, c_10])).
% 2.88/1.45  tff(c_20, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.45  tff(c_202, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_20])).
% 2.88/1.45  tff(c_517, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_202])).
% 2.88/1.45  tff(c_524, plain, (k9_relat_1('#skF_2', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87, c_517])).
% 2.88/1.45  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_144, c_524])).
% 2.88/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.45  
% 2.88/1.45  Inference rules
% 2.88/1.45  ----------------------
% 2.88/1.45  #Ref     : 0
% 2.88/1.45  #Sup     : 137
% 2.88/1.45  #Fact    : 0
% 2.88/1.45  #Define  : 0
% 2.88/1.45  #Split   : 0
% 2.88/1.45  #Chain   : 0
% 2.88/1.45  #Close   : 0
% 2.88/1.45  
% 2.88/1.45  Ordering : KBO
% 2.88/1.45  
% 2.88/1.45  Simplification rules
% 2.88/1.45  ----------------------
% 2.88/1.45  #Subsume      : 0
% 2.88/1.45  #Demod        : 35
% 2.88/1.45  #Tautology    : 46
% 2.88/1.45  #SimpNegUnit  : 0
% 2.88/1.45  #BackRed      : 2
% 2.88/1.45  
% 2.88/1.45  #Partial instantiations: 0
% 2.88/1.45  #Strategies tried      : 1
% 2.88/1.45  
% 2.88/1.45  Timing (in seconds)
% 2.88/1.45  ----------------------
% 2.88/1.46  Preprocessing        : 0.30
% 2.88/1.46  Parsing              : 0.16
% 2.88/1.46  CNF conversion       : 0.02
% 2.88/1.46  Main loop            : 0.37
% 2.88/1.46  Inferencing          : 0.15
% 2.88/1.46  Reduction            : 0.11
% 2.88/1.46  Demodulation         : 0.08
% 2.88/1.46  BG Simplification    : 0.02
% 2.88/1.46  Subsumption          : 0.06
% 2.88/1.46  Abstraction          : 0.02
% 2.88/1.46  MUC search           : 0.00
% 2.88/1.46  Cooper               : 0.00
% 2.88/1.46  Total                : 0.71
% 2.88/1.46  Index Insertion      : 0.00
% 2.88/1.46  Index Deletion       : 0.00
% 2.88/1.46  Index Matching       : 0.00
% 2.88/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
