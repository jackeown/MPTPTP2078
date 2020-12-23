%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 172 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_65,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_97,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_106,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_20,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_204,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden(k4_tarski('#skF_1'(A_95,B_96,C_97),A_95),C_97)
      | ~ r2_hidden(A_95,k9_relat_1(C_97,B_96))
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [C_17,A_15,B_16] :
      ( k1_funct_1(C_17,A_15) = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_233,plain,(
    ! [C_105,A_106,B_107] :
      ( k1_funct_1(C_105,'#skF_1'(A_106,B_107,C_105)) = A_106
      | ~ v1_funct_1(C_105)
      | ~ r2_hidden(A_106,k9_relat_1(C_105,B_107))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_204,c_24])).

tff(c_244,plain,(
    ! [A_14,A_106] :
      ( k1_funct_1(A_14,'#skF_1'(A_106,k1_relat_1(A_14),A_14)) = A_106
      | ~ v1_funct_1(A_14)
      | ~ r2_hidden(A_106,k2_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_233])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_187,plain,(
    ! [A_90,B_91,C_92] :
      ( r2_hidden('#skF_1'(A_90,B_91,C_92),k1_relat_1(C_92))
      | ~ r2_hidden(A_90,k9_relat_1(C_92,B_91))
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [A_57,C_58,B_59] :
      ( m1_subset_1(A_57,C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [A_57,B_2,A_1] :
      ( m1_subset_1(A_57,B_2)
      | ~ r2_hidden(A_57,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_263,plain,(
    ! [A_112,B_113,C_114,B_115] :
      ( m1_subset_1('#skF_1'(A_112,B_113,C_114),B_115)
      | ~ r1_tarski(k1_relat_1(C_114),B_115)
      | ~ r2_hidden(A_112,k9_relat_1(C_114,B_113))
      | ~ v1_relat_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_187,c_139])).

tff(c_267,plain,(
    ! [A_116,B_117,B_118,A_119] :
      ( m1_subset_1('#skF_1'(A_116,B_117,B_118),A_119)
      | ~ r2_hidden(A_116,k9_relat_1(B_118,B_117))
      | ~ v4_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_10,c_263])).

tff(c_409,plain,(
    ! [A_139,A_140,A_141] :
      ( m1_subset_1('#skF_1'(A_139,k1_relat_1(A_140),A_140),A_141)
      | ~ r2_hidden(A_139,k2_relat_1(A_140))
      | ~ v4_relat_1(A_140,A_141)
      | ~ v1_relat_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_267])).

tff(c_36,plain,(
    ! [E_28] :
      ( k1_funct_1('#skF_5',E_28) != '#skF_2'
      | ~ m1_subset_1(E_28,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_465,plain,(
    ! [A_145,A_146] :
      ( k1_funct_1('#skF_5','#skF_1'(A_145,k1_relat_1(A_146),A_146)) != '#skF_2'
      | ~ r2_hidden(A_145,k2_relat_1(A_146))
      | ~ v4_relat_1(A_146,'#skF_3')
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_409,c_36])).

tff(c_469,plain,(
    ! [A_106] :
      ( A_106 != '#skF_2'
      | ~ r2_hidden(A_106,k2_relat_1('#skF_5'))
      | ~ v4_relat_1('#skF_5','#skF_3')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_106,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_465])).

tff(c_472,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_44,c_74,c_106,c_469])).

tff(c_148,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_157,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_148])).

tff(c_38,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_159,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_38])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.86  
% 3.23/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.23/1.86  
% 3.23/1.86  %Foreground sorts:
% 3.23/1.86  
% 3.23/1.86  
% 3.23/1.86  %Background operators:
% 3.23/1.86  
% 3.23/1.86  
% 3.23/1.86  %Foreground operators:
% 3.23/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.23/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.23/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.23/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.86  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.86  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.86  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.23/1.86  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.23/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.23/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.86  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.23/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.86  
% 3.23/1.89  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.23/1.89  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.23/1.89  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.23/1.89  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.23/1.89  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.23/1.89  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.23/1.89  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.23/1.89  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.23/1.89  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.23/1.89  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.23/1.89  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.89  tff(c_65, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.23/1.89  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_65])).
% 3.23/1.89  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.89  tff(c_97, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.89  tff(c_106, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_97])).
% 3.23/1.89  tff(c_20, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.23/1.89  tff(c_204, plain, (![A_95, B_96, C_97]: (r2_hidden(k4_tarski('#skF_1'(A_95, B_96, C_97), A_95), C_97) | ~r2_hidden(A_95, k9_relat_1(C_97, B_96)) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.89  tff(c_24, plain, (![C_17, A_15, B_16]: (k1_funct_1(C_17, A_15)=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.23/1.89  tff(c_233, plain, (![C_105, A_106, B_107]: (k1_funct_1(C_105, '#skF_1'(A_106, B_107, C_105))=A_106 | ~v1_funct_1(C_105) | ~r2_hidden(A_106, k9_relat_1(C_105, B_107)) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_204, c_24])).
% 3.23/1.89  tff(c_244, plain, (![A_14, A_106]: (k1_funct_1(A_14, '#skF_1'(A_106, k1_relat_1(A_14), A_14))=A_106 | ~v1_funct_1(A_14) | ~r2_hidden(A_106, k2_relat_1(A_14)) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_233])).
% 3.23/1.89  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.89  tff(c_187, plain, (![A_90, B_91, C_92]: (r2_hidden('#skF_1'(A_90, B_91, C_92), k1_relat_1(C_92)) | ~r2_hidden(A_90, k9_relat_1(C_92, B_91)) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.89  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.89  tff(c_134, plain, (![A_57, C_58, B_59]: (m1_subset_1(A_57, C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.89  tff(c_139, plain, (![A_57, B_2, A_1]: (m1_subset_1(A_57, B_2) | ~r2_hidden(A_57, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_134])).
% 3.23/1.89  tff(c_263, plain, (![A_112, B_113, C_114, B_115]: (m1_subset_1('#skF_1'(A_112, B_113, C_114), B_115) | ~r1_tarski(k1_relat_1(C_114), B_115) | ~r2_hidden(A_112, k9_relat_1(C_114, B_113)) | ~v1_relat_1(C_114))), inference(resolution, [status(thm)], [c_187, c_139])).
% 3.23/1.89  tff(c_267, plain, (![A_116, B_117, B_118, A_119]: (m1_subset_1('#skF_1'(A_116, B_117, B_118), A_119) | ~r2_hidden(A_116, k9_relat_1(B_118, B_117)) | ~v4_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_10, c_263])).
% 3.23/1.89  tff(c_409, plain, (![A_139, A_140, A_141]: (m1_subset_1('#skF_1'(A_139, k1_relat_1(A_140), A_140), A_141) | ~r2_hidden(A_139, k2_relat_1(A_140)) | ~v4_relat_1(A_140, A_141) | ~v1_relat_1(A_140) | ~v1_relat_1(A_140))), inference(superposition, [status(thm), theory('equality')], [c_20, c_267])).
% 3.23/1.89  tff(c_36, plain, (![E_28]: (k1_funct_1('#skF_5', E_28)!='#skF_2' | ~m1_subset_1(E_28, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.89  tff(c_465, plain, (![A_145, A_146]: (k1_funct_1('#skF_5', '#skF_1'(A_145, k1_relat_1(A_146), A_146))!='#skF_2' | ~r2_hidden(A_145, k2_relat_1(A_146)) | ~v4_relat_1(A_146, '#skF_3') | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_409, c_36])).
% 3.23/1.89  tff(c_469, plain, (![A_106]: (A_106!='#skF_2' | ~r2_hidden(A_106, k2_relat_1('#skF_5')) | ~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~r2_hidden(A_106, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_465])).
% 3.23/1.89  tff(c_472, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_44, c_74, c_106, c_469])).
% 3.23/1.89  tff(c_148, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.23/1.89  tff(c_157, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_148])).
% 3.23/1.89  tff(c_38, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.89  tff(c_159, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_38])).
% 3.23/1.89  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_159])).
% 3.23/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.89  
% 3.23/1.89  Inference rules
% 3.23/1.89  ----------------------
% 3.23/1.89  #Ref     : 0
% 3.23/1.89  #Sup     : 93
% 3.23/1.89  #Fact    : 0
% 3.23/1.89  #Define  : 0
% 3.23/1.89  #Split   : 0
% 3.23/1.89  #Chain   : 0
% 3.23/1.89  #Close   : 0
% 3.23/1.89  
% 3.23/1.89  Ordering : KBO
% 3.23/1.89  
% 3.23/1.89  Simplification rules
% 3.23/1.89  ----------------------
% 3.23/1.89  #Subsume      : 2
% 3.23/1.89  #Demod        : 11
% 3.23/1.89  #Tautology    : 15
% 3.23/1.89  #SimpNegUnit  : 1
% 3.23/1.89  #BackRed      : 3
% 3.23/1.89  
% 3.23/1.89  #Partial instantiations: 0
% 3.23/1.89  #Strategies tried      : 1
% 3.23/1.89  
% 3.23/1.89  Timing (in seconds)
% 3.23/1.89  ----------------------
% 3.23/1.89  Preprocessing        : 0.52
% 3.23/1.89  Parsing              : 0.27
% 3.23/1.89  CNF conversion       : 0.04
% 3.23/1.89  Main loop            : 0.46
% 3.23/1.89  Inferencing          : 0.18
% 3.23/1.89  Reduction            : 0.11
% 3.23/1.89  Demodulation         : 0.09
% 3.23/1.89  BG Simplification    : 0.03
% 3.23/1.89  Subsumption          : 0.09
% 3.23/1.89  Abstraction          : 0.03
% 3.23/1.89  MUC search           : 0.00
% 3.23/1.89  Cooper               : 0.00
% 3.23/1.89  Total                : 1.03
% 3.23/1.89  Index Insertion      : 0.00
% 3.23/1.89  Index Deletion       : 0.00
% 3.23/1.89  Index Matching       : 0.00
% 3.23/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
