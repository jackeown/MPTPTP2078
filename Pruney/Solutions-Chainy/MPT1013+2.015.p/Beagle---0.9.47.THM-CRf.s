%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:36 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 195 expanded)
%              Number of equality atoms :   29 (  78 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,(
    ! [D_63,A_65,C_67,B_64,F_66,E_68] :
      ( k4_relset_1(A_65,B_64,C_67,D_63,E_68,F_66) = k5_relat_1(E_68,F_66)
      | ~ m1_subset_1(F_66,k1_zfmisc_1(k2_zfmisc_1(C_67,D_63)))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_295,plain,(
    ! [A_73,B_74,E_75] :
      ( k4_relset_1(A_73,B_74,'#skF_1','#skF_1',E_75,'#skF_2') = k5_relat_1(E_75,'#skF_2')
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_30,c_235])).

tff(c_313,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_295])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_325,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_22])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_67,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_26,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_84,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_97,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_91])).

tff(c_100,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_152,plain,(
    ! [A_55,B_56,C_57] :
      ( m1_subset_1(k1_relset_1(A_55,B_56,C_57),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,
    ( m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_152])).

tff(c_180,plain,(
    m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_172])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_211,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_63,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_94,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_84])).

tff(c_99,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_94])).

tff(c_193,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k5_relat_1(B_58,A_59)) = k2_relat_1(A_59)
      | ~ r1_tarski(k1_relat_1(A_59),k2_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_196,plain,(
    ! [A_59] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_59)) = k2_relat_1(A_59)
      | ~ r1_tarski(k1_relat_1(A_59),'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_193])).

tff(c_275,plain,(
    ! [A_72] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_72)) = k2_relat_1(A_72)
      | ~ r1_tarski(k1_relat_1(A_72),'#skF_1')
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_196])).

tff(c_278,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_211,c_275])).

tff(c_284,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_97,c_278])).

tff(c_343,plain,(
    ! [A_82,C_80,E_77,B_81,F_78,D_79] :
      ( m1_subset_1(k4_relset_1(A_82,B_81,C_80,D_79,E_77,F_78),k1_zfmisc_1(k2_zfmisc_1(A_82,D_79)))
      | ~ m1_subset_1(F_78,k1_zfmisc_1(k2_zfmisc_1(C_80,D_79)))
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_365,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_343])).

tff(c_379,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_365])).

tff(c_18,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_408,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_379,c_18])).

tff(c_420,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_408])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:40:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.60  
% 2.60/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.60  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.60  
% 2.60/1.60  %Foreground sorts:
% 2.60/1.60  
% 2.60/1.60  
% 2.60/1.60  %Background operators:
% 2.60/1.60  
% 2.60/1.60  
% 2.60/1.60  %Foreground operators:
% 2.60/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.60/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.60/1.60  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.60  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.60  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.60  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.60/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.60  
% 2.96/1.62  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 2.96/1.62  tff(f_71, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.96/1.62  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.96/1.62  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.96/1.62  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.96/1.62  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.96/1.62  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.96/1.62  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.96/1.62  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.96/1.62  tff(f_57, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.96/1.62  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.62  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.62  tff(c_235, plain, (![D_63, A_65, C_67, B_64, F_66, E_68]: (k4_relset_1(A_65, B_64, C_67, D_63, E_68, F_66)=k5_relat_1(E_68, F_66) | ~m1_subset_1(F_66, k1_zfmisc_1(k2_zfmisc_1(C_67, D_63))) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.96/1.62  tff(c_295, plain, (![A_73, B_74, E_75]: (k4_relset_1(A_73, B_74, '#skF_1', '#skF_1', E_75, '#skF_2')=k5_relat_1(E_75, '#skF_2') | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_30, c_235])).
% 2.96/1.62  tff(c_313, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_295])).
% 2.96/1.62  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.62  tff(c_325, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_22])).
% 2.96/1.62  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.62  tff(c_54, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.96/1.62  tff(c_60, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_54])).
% 2.96/1.62  tff(c_67, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_60])).
% 2.96/1.62  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.62  tff(c_84, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.62  tff(c_91, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_84])).
% 2.96/1.62  tff(c_97, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_91])).
% 2.96/1.62  tff(c_100, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.62  tff(c_112, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_100])).
% 2.96/1.62  tff(c_152, plain, (![A_55, B_56, C_57]: (m1_subset_1(k1_relset_1(A_55, B_56, C_57), k1_zfmisc_1(A_55)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.62  tff(c_172, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_112, c_152])).
% 2.96/1.62  tff(c_180, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_172])).
% 2.96/1.62  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.62  tff(c_211, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_180, c_2])).
% 2.96/1.62  tff(c_63, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_54])).
% 2.96/1.62  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_63])).
% 2.96/1.62  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.62  tff(c_94, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_84])).
% 2.96/1.62  tff(c_99, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_94])).
% 2.96/1.62  tff(c_193, plain, (![B_58, A_59]: (k2_relat_1(k5_relat_1(B_58, A_59))=k2_relat_1(A_59) | ~r1_tarski(k1_relat_1(A_59), k2_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.62  tff(c_196, plain, (![A_59]: (k2_relat_1(k5_relat_1('#skF_3', A_59))=k2_relat_1(A_59) | ~r1_tarski(k1_relat_1(A_59), '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_99, c_193])).
% 2.96/1.62  tff(c_275, plain, (![A_72]: (k2_relat_1(k5_relat_1('#skF_3', A_72))=k2_relat_1(A_72) | ~r1_tarski(k1_relat_1(A_72), '#skF_1') | ~v1_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_196])).
% 2.96/1.62  tff(c_278, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_211, c_275])).
% 2.96/1.62  tff(c_284, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_97, c_278])).
% 2.96/1.62  tff(c_343, plain, (![A_82, C_80, E_77, B_81, F_78, D_79]: (m1_subset_1(k4_relset_1(A_82, B_81, C_80, D_79, E_77, F_78), k1_zfmisc_1(k2_zfmisc_1(A_82, D_79))) | ~m1_subset_1(F_78, k1_zfmisc_1(k2_zfmisc_1(C_80, D_79))) | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.96/1.62  tff(c_365, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_313, c_343])).
% 2.96/1.62  tff(c_379, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_365])).
% 2.96/1.62  tff(c_18, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.62  tff(c_408, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_379, c_18])).
% 2.96/1.62  tff(c_420, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_408])).
% 2.96/1.62  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_420])).
% 2.96/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.62  
% 2.96/1.62  Inference rules
% 2.96/1.62  ----------------------
% 2.96/1.62  #Ref     : 0
% 2.96/1.62  #Sup     : 97
% 2.96/1.62  #Fact    : 0
% 2.96/1.62  #Define  : 0
% 2.96/1.62  #Split   : 2
% 2.96/1.62  #Chain   : 0
% 2.96/1.62  #Close   : 0
% 2.96/1.62  
% 2.96/1.62  Ordering : KBO
% 2.96/1.62  
% 2.96/1.62  Simplification rules
% 2.96/1.62  ----------------------
% 2.96/1.62  #Subsume      : 3
% 2.96/1.62  #Demod        : 41
% 2.96/1.62  #Tautology    : 35
% 2.96/1.62  #SimpNegUnit  : 1
% 2.96/1.62  #BackRed      : 1
% 2.96/1.62  
% 2.96/1.62  #Partial instantiations: 0
% 2.96/1.62  #Strategies tried      : 1
% 2.96/1.62  
% 2.96/1.62  Timing (in seconds)
% 2.96/1.62  ----------------------
% 2.96/1.62  Preprocessing        : 0.39
% 2.96/1.62  Parsing              : 0.19
% 2.96/1.62  CNF conversion       : 0.02
% 2.96/1.62  Main loop            : 0.36
% 2.96/1.63  Inferencing          : 0.14
% 2.96/1.63  Reduction            : 0.10
% 2.96/1.63  Demodulation         : 0.08
% 2.96/1.63  BG Simplification    : 0.02
% 2.96/1.63  Subsumption          : 0.06
% 2.96/1.63  Abstraction          : 0.03
% 2.96/1.63  MUC search           : 0.00
% 2.96/1.63  Cooper               : 0.00
% 2.96/1.63  Total                : 0.79
% 2.96/1.63  Index Insertion      : 0.00
% 2.96/1.63  Index Deletion       : 0.00
% 2.96/1.63  Index Matching       : 0.00
% 2.96/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
