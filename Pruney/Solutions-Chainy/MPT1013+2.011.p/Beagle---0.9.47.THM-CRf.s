%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:35 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 187 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_83,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_49,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_53,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_26,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_77,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_relset_1(A_44,B_45,C_46) = k2_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_85,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_80])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_46])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_83,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_87,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_83])).

tff(c_96,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(k5_relat_1(B_47,A_48)) = k2_relat_1(A_48)
      | ~ r1_tarski(k1_relat_1(A_48),k2_relat_1(B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [A_48] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_48)) = k2_relat_1(A_48)
      | ~ r1_tarski(k1_relat_1(A_48),'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_96])).

tff(c_130,plain,(
    ! [A_51] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_51)) = k2_relat_1(A_51)
      | ~ r1_tarski(k1_relat_1(A_51),'#skF_1')
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_102])).

tff(c_135,plain,(
    ! [B_5] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_5)) = k2_relat_1(B_5)
      | ~ v4_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_148,plain,(
    ! [E_55,A_58,B_56,F_54,C_53,D_57] :
      ( k4_relset_1(A_58,B_56,C_53,D_57,E_55,F_54) = k5_relat_1(E_55,F_54)
      | ~ m1_subset_1(F_54,k1_zfmisc_1(k2_zfmisc_1(C_53,D_57)))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(A_58,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_172,plain,(
    ! [A_61,B_62,E_63] :
      ( k4_relset_1(A_61,B_62,'#skF_1','#skF_1',E_63,'#skF_2') = k5_relat_1(E_63,'#skF_2')
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_180,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_172])).

tff(c_222,plain,(
    ! [A_74,F_70,B_73,C_72,E_69,D_71] :
      ( m1_subset_1(k4_relset_1(A_74,B_73,C_72,D_71,E_69,F_70),k1_zfmisc_1(k2_zfmisc_1(A_74,D_71)))
      | ~ m1_subset_1(F_70,k1_zfmisc_1(k2_zfmisc_1(C_72,D_71)))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_251,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_222])).

tff(c_269,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_251])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] :
      ( k2_relset_1(A_20,B_21,C_22) = k2_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_381,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_269,c_18])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_185,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_22])).

tff(c_512,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_185])).

tff(c_541,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | ~ v4_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_512])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_60,c_85,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n001.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 20:22:00 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.34  
% 2.75/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.34  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.34  
% 2.75/1.34  %Foreground sorts:
% 2.75/1.34  
% 2.75/1.34  
% 2.75/1.34  %Background operators:
% 2.75/1.34  
% 2.75/1.34  
% 2.75/1.34  %Foreground operators:
% 2.75/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.75/1.34  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.75/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.75/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.34  
% 2.75/1.35  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.75/1.35  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_2)).
% 2.75/1.35  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.75/1.35  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.75/1.35  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.75/1.35  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.75/1.35  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.75/1.35  tff(f_71, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.75/1.35  tff(f_61, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.75/1.35  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.35  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.35  tff(c_40, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.35  tff(c_43, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 2.75/1.35  tff(c_49, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 2.75/1.35  tff(c_53, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.35  tff(c_60, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_53])).
% 2.75/1.35  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.35  tff(c_77, plain, (![A_44, B_45, C_46]: (k2_relset_1(A_44, B_45, C_46)=k2_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.75/1.35  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_77])).
% 2.75/1.35  tff(c_85, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_80])).
% 2.75/1.35  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.75/1.35  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.35  tff(c_46, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.75/1.35  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 2.75/1.35  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.35  tff(c_83, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_77])).
% 2.75/1.35  tff(c_87, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_83])).
% 2.75/1.35  tff(c_96, plain, (![B_47, A_48]: (k2_relat_1(k5_relat_1(B_47, A_48))=k2_relat_1(A_48) | ~r1_tarski(k1_relat_1(A_48), k2_relat_1(B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.35  tff(c_102, plain, (![A_48]: (k2_relat_1(k5_relat_1('#skF_3', A_48))=k2_relat_1(A_48) | ~r1_tarski(k1_relat_1(A_48), '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_87, c_96])).
% 2.75/1.35  tff(c_130, plain, (![A_51]: (k2_relat_1(k5_relat_1('#skF_3', A_51))=k2_relat_1(A_51) | ~r1_tarski(k1_relat_1(A_51), '#skF_1') | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_102])).
% 2.75/1.35  tff(c_135, plain, (![B_5]: (k2_relat_1(k5_relat_1('#skF_3', B_5))=k2_relat_1(B_5) | ~v4_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_130])).
% 2.75/1.35  tff(c_148, plain, (![E_55, A_58, B_56, F_54, C_53, D_57]: (k4_relset_1(A_58, B_56, C_53, D_57, E_55, F_54)=k5_relat_1(E_55, F_54) | ~m1_subset_1(F_54, k1_zfmisc_1(k2_zfmisc_1(C_53, D_57))) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(A_58, B_56))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.35  tff(c_172, plain, (![A_61, B_62, E_63]: (k4_relset_1(A_61, B_62, '#skF_1', '#skF_1', E_63, '#skF_2')=k5_relat_1(E_63, '#skF_2') | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(resolution, [status(thm)], [c_30, c_148])).
% 2.75/1.35  tff(c_180, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_172])).
% 2.75/1.35  tff(c_222, plain, (![A_74, F_70, B_73, C_72, E_69, D_71]: (m1_subset_1(k4_relset_1(A_74, B_73, C_72, D_71, E_69, F_70), k1_zfmisc_1(k2_zfmisc_1(A_74, D_71))) | ~m1_subset_1(F_70, k1_zfmisc_1(k2_zfmisc_1(C_72, D_71))) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.35  tff(c_251, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_180, c_222])).
% 2.75/1.35  tff(c_269, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_251])).
% 2.75/1.35  tff(c_18, plain, (![A_20, B_21, C_22]: (k2_relset_1(A_20, B_21, C_22)=k2_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.75/1.35  tff(c_381, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_269, c_18])).
% 2.75/1.35  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.35  tff(c_185, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_22])).
% 2.75/1.35  tff(c_512, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_381, c_185])).
% 2.75/1.35  tff(c_541, plain, (k2_relat_1('#skF_2')!='#skF_1' | ~v4_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135, c_512])).
% 2.75/1.35  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_60, c_85, c_541])).
% 2.75/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.35  
% 2.75/1.35  Inference rules
% 2.75/1.35  ----------------------
% 2.75/1.35  #Ref     : 0
% 2.75/1.35  #Sup     : 134
% 2.75/1.35  #Fact    : 0
% 2.75/1.35  #Define  : 0
% 2.75/1.35  #Split   : 0
% 2.75/1.35  #Chain   : 0
% 2.75/1.35  #Close   : 0
% 2.75/1.36  
% 2.75/1.36  Ordering : KBO
% 2.75/1.36  
% 2.75/1.36  Simplification rules
% 2.75/1.36  ----------------------
% 2.75/1.36  #Subsume      : 2
% 2.75/1.36  #Demod        : 37
% 2.75/1.36  #Tautology    : 35
% 2.75/1.36  #SimpNegUnit  : 0
% 2.75/1.36  #BackRed      : 2
% 2.75/1.36  
% 2.75/1.36  #Partial instantiations: 0
% 2.75/1.36  #Strategies tried      : 1
% 2.75/1.36  
% 2.75/1.36  Timing (in seconds)
% 2.75/1.36  ----------------------
% 2.75/1.36  Preprocessing        : 0.30
% 2.75/1.36  Parsing              : 0.17
% 2.75/1.36  CNF conversion       : 0.02
% 2.75/1.36  Main loop            : 0.31
% 2.75/1.36  Inferencing          : 0.12
% 2.75/1.36  Reduction            : 0.09
% 2.75/1.36  Demodulation         : 0.07
% 2.75/1.36  BG Simplification    : 0.02
% 2.75/1.36  Subsumption          : 0.06
% 2.75/1.36  Abstraction          : 0.02
% 2.75/1.36  MUC search           : 0.00
% 2.75/1.36  Cooper               : 0.00
% 2.75/1.36  Total                : 0.65
% 2.75/1.36  Index Insertion      : 0.00
% 2.75/1.36  Index Deletion       : 0.00
% 2.75/1.36  Index Matching       : 0.00
% 2.75/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
