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
% DateTime   : Thu Dec  3 10:15:34 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 175 expanded)
%              Number of equality atoms :   26 (  72 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_37,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_55,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_70,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_78,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_73])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_80,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_76])).

tff(c_89,plain,(
    ! [B_44,A_45] :
      ( k2_relat_1(k5_relat_1(B_44,A_45)) = k2_relat_1(A_45)
      | ~ r1_tarski(k1_relat_1(A_45),k2_relat_1(B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    ! [A_45] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_45)) = k2_relat_1(A_45)
      | ~ r1_tarski(k1_relat_1(A_45),'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_89])).

tff(c_105,plain,(
    ! [A_46] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_46)) = k2_relat_1(A_46)
      | ~ r1_tarski(k1_relat_1(A_46),'#skF_1')
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_92])).

tff(c_110,plain,(
    ! [B_2] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_2)) = k2_relat_1(B_2)
      | ~ v4_relat_1(B_2,'#skF_1')
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_158,plain,(
    ! [B_56,E_57,D_53,A_52,F_55,C_54] :
      ( k4_relset_1(A_52,B_56,C_54,D_53,E_57,F_55) = k5_relat_1(E_57,F_55)
      | ~ m1_subset_1(F_55,k1_zfmisc_1(k2_zfmisc_1(C_54,D_53)))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(A_52,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_165,plain,(
    ! [A_58,B_59,E_60] :
      ( k4_relset_1(A_58,B_59,'#skF_1','#skF_1',E_60,'#skF_2') = k5_relat_1(E_60,'#skF_2')
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(resolution,[status(thm)],[c_28,c_158])).

tff(c_173,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_165])).

tff(c_230,plain,(
    ! [C_73,B_68,F_72,E_70,A_69,D_71] :
      ( m1_subset_1(k4_relset_1(A_69,B_68,C_73,D_71,E_70,F_72),k1_zfmisc_1(k2_zfmisc_1(A_69,D_71)))
      | ~ m1_subset_1(F_72,k1_zfmisc_1(k2_zfmisc_1(C_73,D_71)))
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_259,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_230])).

tff(c_275,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_259])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_445,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_275,c_16])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_20])).

tff(c_510,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_178])).

tff(c_517,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | ~ v4_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_510])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62,c_78,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n013.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 16:32:09 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.33  
% 2.45/1.33  %Foreground sorts:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Background operators:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Foreground operators:
% 2.45/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.45/1.33  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.33  
% 2.45/1.35  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_2)).
% 2.45/1.35  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.45/1.35  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.45/1.35  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.45/1.35  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.45/1.35  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.45/1.35  tff(f_66, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.45/1.35  tff(f_56, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.45/1.35  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_37, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.45/1.35  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_37])).
% 2.45/1.35  tff(c_55, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.35  tff(c_62, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_55])).
% 2.45/1.35  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_70, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.45/1.35  tff(c_73, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_70])).
% 2.45/1.35  tff(c_78, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_73])).
% 2.45/1.35  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.35  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_45, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_37])).
% 2.45/1.35  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_70])).
% 2.45/1.35  tff(c_80, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_76])).
% 2.45/1.35  tff(c_89, plain, (![B_44, A_45]: (k2_relat_1(k5_relat_1(B_44, A_45))=k2_relat_1(A_45) | ~r1_tarski(k1_relat_1(A_45), k2_relat_1(B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.45/1.35  tff(c_92, plain, (![A_45]: (k2_relat_1(k5_relat_1('#skF_3', A_45))=k2_relat_1(A_45) | ~r1_tarski(k1_relat_1(A_45), '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_80, c_89])).
% 2.45/1.35  tff(c_105, plain, (![A_46]: (k2_relat_1(k5_relat_1('#skF_3', A_46))=k2_relat_1(A_46) | ~r1_tarski(k1_relat_1(A_46), '#skF_1') | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_92])).
% 2.45/1.35  tff(c_110, plain, (![B_2]: (k2_relat_1(k5_relat_1('#skF_3', B_2))=k2_relat_1(B_2) | ~v4_relat_1(B_2, '#skF_1') | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_105])).
% 2.45/1.35  tff(c_158, plain, (![B_56, E_57, D_53, A_52, F_55, C_54]: (k4_relset_1(A_52, B_56, C_54, D_53, E_57, F_55)=k5_relat_1(E_57, F_55) | ~m1_subset_1(F_55, k1_zfmisc_1(k2_zfmisc_1(C_54, D_53))) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(A_52, B_56))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.45/1.35  tff(c_165, plain, (![A_58, B_59, E_60]: (k4_relset_1(A_58, B_59, '#skF_1', '#skF_1', E_60, '#skF_2')=k5_relat_1(E_60, '#skF_2') | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(resolution, [status(thm)], [c_28, c_158])).
% 2.45/1.35  tff(c_173, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_165])).
% 2.45/1.35  tff(c_230, plain, (![C_73, B_68, F_72, E_70, A_69, D_71]: (m1_subset_1(k4_relset_1(A_69, B_68, C_73, D_71, E_70, F_72), k1_zfmisc_1(k2_zfmisc_1(A_69, D_71))) | ~m1_subset_1(F_72, k1_zfmisc_1(k2_zfmisc_1(C_73, D_71))) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.45/1.35  tff(c_259, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_173, c_230])).
% 2.45/1.35  tff(c_275, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_259])).
% 2.45/1.35  tff(c_16, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.45/1.35  tff(c_445, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_275, c_16])).
% 2.45/1.35  tff(c_20, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_178, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_20])).
% 2.45/1.35  tff(c_510, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_178])).
% 2.45/1.35  tff(c_517, plain, (k2_relat_1('#skF_2')!='#skF_1' | ~v4_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_110, c_510])).
% 2.45/1.35  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_62, c_78, c_517])).
% 2.45/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  Inference rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Ref     : 0
% 2.45/1.35  #Sup     : 131
% 2.45/1.35  #Fact    : 0
% 2.45/1.35  #Define  : 0
% 2.45/1.35  #Split   : 0
% 2.45/1.35  #Chain   : 0
% 2.45/1.35  #Close   : 0
% 2.45/1.35  
% 2.45/1.35  Ordering : KBO
% 2.45/1.35  
% 2.45/1.35  Simplification rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Subsume      : 2
% 2.45/1.35  #Demod        : 30
% 2.45/1.35  #Tautology    : 37
% 2.45/1.35  #SimpNegUnit  : 0
% 2.45/1.35  #BackRed      : 2
% 2.45/1.35  
% 2.45/1.35  #Partial instantiations: 0
% 2.45/1.35  #Strategies tried      : 1
% 2.45/1.35  
% 2.45/1.35  Timing (in seconds)
% 2.45/1.35  ----------------------
% 2.75/1.35  Preprocessing        : 0.29
% 2.75/1.35  Parsing              : 0.16
% 2.75/1.35  CNF conversion       : 0.02
% 2.75/1.35  Main loop            : 0.32
% 2.75/1.35  Inferencing          : 0.13
% 2.75/1.35  Reduction            : 0.09
% 2.75/1.35  Demodulation         : 0.06
% 2.75/1.35  BG Simplification    : 0.02
% 2.75/1.35  Subsumption          : 0.06
% 2.75/1.35  Abstraction          : 0.02
% 2.75/1.35  MUC search           : 0.00
% 2.75/1.35  Cooper               : 0.00
% 2.75/1.35  Total                : 0.64
% 2.75/1.35  Index Insertion      : 0.00
% 2.75/1.35  Index Deletion       : 0.00
% 2.75/1.35  Index Matching       : 0.00
% 2.75/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
