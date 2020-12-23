%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:03 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 213 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_47,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_51,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_140,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(k4_tarski('#skF_1'(A_78,B_79,C_80),A_78),C_80)
      | ~ r2_hidden(A_78,k9_relat_1(C_80,B_79))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_253,plain,(
    ! [C_92,A_93,B_94] :
      ( k1_funct_1(C_92,'#skF_1'(A_93,B_94,C_92)) = A_93
      | ~ v1_funct_1(C_92)
      | ~ r2_hidden(A_93,k9_relat_1(C_92,B_94))
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_140,c_24])).

tff(c_264,plain,(
    ! [A_17,A_93] :
      ( k1_funct_1(A_17,'#skF_1'(A_93,k1_relat_1(A_17),A_17)) = A_93
      | ~ v1_funct_1(A_17)
      | ~ r2_hidden(A_93,k2_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_253])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden('#skF_1'(A_11,B_12,C_13),k1_relat_1(C_13))
      | ~ r2_hidden(A_11,k9_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,(
    ! [A_81,C_82] :
      ( r2_hidden(k4_tarski(A_81,k1_funct_1(C_82,A_81)),C_82)
      | ~ r2_hidden(A_81,k1_relat_1(C_82))
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_432,plain,(
    ! [A_130,C_131,A_132] :
      ( r2_hidden(k4_tarski(A_130,k1_funct_1(C_131,A_130)),A_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(A_132))
      | ~ r2_hidden(A_130,k1_relat_1(C_131))
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_170,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_492,plain,(
    ! [A_135,C_136,C_137,D_138] :
      ( r2_hidden(A_135,C_136)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(C_136,D_138)))
      | ~ r2_hidden(A_135,k1_relat_1(C_137))
      | ~ v1_funct_1(C_137)
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_432,c_6])).

tff(c_500,plain,(
    ! [A_135] :
      ( r2_hidden(A_135,'#skF_3')
      | ~ r2_hidden(A_135,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_492])).

tff(c_506,plain,(
    ! [A_139] :
      ( r2_hidden(A_139,'#skF_3')
      | ~ r2_hidden(A_139,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_40,c_500])).

tff(c_526,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12,'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_11,k9_relat_1('#skF_5',B_12))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_506])).

tff(c_539,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(A_140,B_141,'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_140,k9_relat_1('#skF_5',B_141)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_526])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_550,plain,(
    ! [A_142,B_143] :
      ( m1_subset_1('#skF_1'(A_142,B_143,'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_142,k9_relat_1('#skF_5',B_143)) ) ),
    inference(resolution,[status(thm)],[c_539,c_10])).

tff(c_578,plain,(
    ! [A_142] :
      ( m1_subset_1('#skF_1'(A_142,k1_relat_1('#skF_5'),'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_142,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_550])).

tff(c_589,plain,(
    ! [A_144] :
      ( m1_subset_1('#skF_1'(A_144,k1_relat_1('#skF_5'),'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_144,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_578])).

tff(c_32,plain,(
    ! [E_28] :
      ( k1_funct_1('#skF_5',E_28) != '#skF_2'
      | ~ m1_subset_1(E_28,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_642,plain,(
    ! [A_149] :
      ( k1_funct_1('#skF_5','#skF_1'(A_149,k1_relat_1('#skF_5'),'#skF_5')) != '#skF_2'
      | ~ r2_hidden(A_149,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_589,c_32])).

tff(c_646,plain,(
    ! [A_93] :
      ( A_93 != '#skF_2'
      | ~ r2_hidden(A_93,k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_93,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_642])).

tff(c_649,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_51,c_40,c_646])).

tff(c_68,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_68])).

tff(c_34,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_76,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34])).

tff(c_651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.75/1.41  
% 2.75/1.41  %Foreground sorts:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Background operators:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Foreground operators:
% 2.75/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.75/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.75/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.41  
% 2.75/1.42  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.75/1.42  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.75/1.42  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.75/1.42  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.75/1.42  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.75/1.42  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.75/1.42  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.75/1.42  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.75/1.42  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.75/1.42  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.75/1.42  tff(c_47, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.42  tff(c_51, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_47])).
% 2.75/1.42  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.75/1.42  tff(c_20, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.75/1.42  tff(c_140, plain, (![A_78, B_79, C_80]: (r2_hidden(k4_tarski('#skF_1'(A_78, B_79, C_80), A_78), C_80) | ~r2_hidden(A_78, k9_relat_1(C_80, B_79)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.42  tff(c_24, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.42  tff(c_253, plain, (![C_92, A_93, B_94]: (k1_funct_1(C_92, '#skF_1'(A_93, B_94, C_92))=A_93 | ~v1_funct_1(C_92) | ~r2_hidden(A_93, k9_relat_1(C_92, B_94)) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_140, c_24])).
% 2.75/1.42  tff(c_264, plain, (![A_17, A_93]: (k1_funct_1(A_17, '#skF_1'(A_93, k1_relat_1(A_17), A_17))=A_93 | ~v1_funct_1(A_17) | ~r2_hidden(A_93, k2_relat_1(A_17)) | ~v1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_253])).
% 2.75/1.42  tff(c_18, plain, (![A_11, B_12, C_13]: (r2_hidden('#skF_1'(A_11, B_12, C_13), k1_relat_1(C_13)) | ~r2_hidden(A_11, k9_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.42  tff(c_170, plain, (![A_81, C_82]: (r2_hidden(k4_tarski(A_81, k1_funct_1(C_82, A_81)), C_82) | ~r2_hidden(A_81, k1_relat_1(C_82)) | ~v1_funct_1(C_82) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.42  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.75/1.42  tff(c_432, plain, (![A_130, C_131, A_132]: (r2_hidden(k4_tarski(A_130, k1_funct_1(C_131, A_130)), A_132) | ~m1_subset_1(C_131, k1_zfmisc_1(A_132)) | ~r2_hidden(A_130, k1_relat_1(C_131)) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_170, c_8])).
% 2.75/1.42  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.42  tff(c_492, plain, (![A_135, C_136, C_137, D_138]: (r2_hidden(A_135, C_136) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(C_136, D_138))) | ~r2_hidden(A_135, k1_relat_1(C_137)) | ~v1_funct_1(C_137) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_432, c_6])).
% 2.75/1.42  tff(c_500, plain, (![A_135]: (r2_hidden(A_135, '#skF_3') | ~r2_hidden(A_135, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_492])).
% 2.75/1.42  tff(c_506, plain, (![A_139]: (r2_hidden(A_139, '#skF_3') | ~r2_hidden(A_139, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_40, c_500])).
% 2.75/1.42  tff(c_526, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12, '#skF_5'), '#skF_3') | ~r2_hidden(A_11, k9_relat_1('#skF_5', B_12)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_506])).
% 2.75/1.42  tff(c_539, plain, (![A_140, B_141]: (r2_hidden('#skF_1'(A_140, B_141, '#skF_5'), '#skF_3') | ~r2_hidden(A_140, k9_relat_1('#skF_5', B_141)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_526])).
% 2.75/1.42  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.75/1.42  tff(c_550, plain, (![A_142, B_143]: (m1_subset_1('#skF_1'(A_142, B_143, '#skF_5'), '#skF_3') | ~r2_hidden(A_142, k9_relat_1('#skF_5', B_143)))), inference(resolution, [status(thm)], [c_539, c_10])).
% 2.75/1.42  tff(c_578, plain, (![A_142]: (m1_subset_1('#skF_1'(A_142, k1_relat_1('#skF_5'), '#skF_5'), '#skF_3') | ~r2_hidden(A_142, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_550])).
% 2.75/1.42  tff(c_589, plain, (![A_144]: (m1_subset_1('#skF_1'(A_144, k1_relat_1('#skF_5'), '#skF_5'), '#skF_3') | ~r2_hidden(A_144, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_578])).
% 2.75/1.42  tff(c_32, plain, (![E_28]: (k1_funct_1('#skF_5', E_28)!='#skF_2' | ~m1_subset_1(E_28, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.75/1.42  tff(c_642, plain, (![A_149]: (k1_funct_1('#skF_5', '#skF_1'(A_149, k1_relat_1('#skF_5'), '#skF_5'))!='#skF_2' | ~r2_hidden(A_149, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_589, c_32])).
% 2.75/1.42  tff(c_646, plain, (![A_93]: (A_93!='#skF_2' | ~r2_hidden(A_93, k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~r2_hidden(A_93, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_642])).
% 2.75/1.42  tff(c_649, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_51, c_40, c_646])).
% 2.75/1.42  tff(c_68, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.75/1.42  tff(c_72, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_68])).
% 2.75/1.42  tff(c_34, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.75/1.42  tff(c_76, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34])).
% 2.75/1.42  tff(c_651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_76])).
% 2.75/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.42  
% 2.75/1.42  Inference rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Ref     : 0
% 2.75/1.42  #Sup     : 135
% 2.75/1.42  #Fact    : 0
% 2.75/1.42  #Define  : 0
% 2.75/1.42  #Split   : 1
% 2.75/1.42  #Chain   : 0
% 2.75/1.42  #Close   : 0
% 2.75/1.42  
% 2.75/1.42  Ordering : KBO
% 2.75/1.42  
% 2.75/1.42  Simplification rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Subsume      : 4
% 2.75/1.42  #Demod        : 12
% 2.75/1.42  #Tautology    : 11
% 2.75/1.42  #SimpNegUnit  : 1
% 2.75/1.42  #BackRed      : 4
% 2.75/1.42  
% 2.75/1.42  #Partial instantiations: 0
% 2.75/1.42  #Strategies tried      : 1
% 2.75/1.42  
% 2.75/1.42  Timing (in seconds)
% 2.75/1.42  ----------------------
% 2.75/1.42  Preprocessing        : 0.31
% 2.75/1.42  Parsing              : 0.16
% 2.75/1.42  CNF conversion       : 0.02
% 2.75/1.42  Main loop            : 0.34
% 2.75/1.42  Inferencing          : 0.14
% 2.75/1.42  Reduction            : 0.08
% 2.75/1.42  Demodulation         : 0.06
% 2.75/1.42  BG Simplification    : 0.02
% 2.75/1.42  Subsumption          : 0.07
% 2.75/1.42  Abstraction          : 0.02
% 2.75/1.42  MUC search           : 0.00
% 2.75/1.42  Cooper               : 0.00
% 2.75/1.42  Total                : 0.68
% 2.75/1.42  Index Insertion      : 0.00
% 2.75/1.42  Index Deletion       : 0.00
% 2.75/1.42  Index Matching       : 0.00
% 2.75/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
