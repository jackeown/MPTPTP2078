%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 137 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 335 expanded)
%              Number of equality atoms :   14 (  41 expanded)
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

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_120,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_129,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_120])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_225,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden(k4_tarski('#skF_1'(A_102,B_103,C_104),A_102),C_104)
      | ~ r2_hidden(A_102,k9_relat_1(C_104,B_103))
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_346,plain,(
    ! [C_119,A_120,B_121] :
      ( k1_funct_1(C_119,'#skF_1'(A_120,B_121,C_119)) = A_120
      | ~ v1_funct_1(C_119)
      | ~ r2_hidden(A_120,k9_relat_1(C_119,B_121))
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_225,c_26])).

tff(c_357,plain,(
    ! [A_17,A_120] :
      ( k1_funct_1(A_17,'#skF_1'(A_120,k1_relat_1(A_17),A_17)) = A_120
      | ~ v1_funct_1(A_17)
      | ~ r2_hidden(A_120,k2_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_346])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_216,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden('#skF_1'(A_96,B_97,C_98),k1_relat_1(C_98))
      | ~ r2_hidden(A_96,k9_relat_1(C_98,B_97))
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_381,plain,(
    ! [A_128,B_129,C_130,A_131] :
      ( r2_hidden('#skF_1'(A_128,B_129,C_130),A_131)
      | ~ m1_subset_1(k1_relat_1(C_130),k1_zfmisc_1(A_131))
      | ~ r2_hidden(A_128,k9_relat_1(C_130,B_129))
      | ~ v1_relat_1(C_130) ) ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_435,plain,(
    ! [A_138,B_139,C_140,B_141] :
      ( r2_hidden('#skF_1'(A_138,B_139,C_140),B_141)
      | ~ r2_hidden(A_138,k9_relat_1(C_140,B_139))
      | ~ v1_relat_1(C_140)
      | ~ r1_tarski(k1_relat_1(C_140),B_141) ) ),
    inference(resolution,[status(thm)],[c_8,c_381])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_459,plain,(
    ! [A_144,B_145,C_146,B_147] :
      ( m1_subset_1('#skF_1'(A_144,B_145,C_146),B_147)
      | ~ r2_hidden(A_144,k9_relat_1(C_146,B_145))
      | ~ v1_relat_1(C_146)
      | ~ r1_tarski(k1_relat_1(C_146),B_147) ) ),
    inference(resolution,[status(thm)],[c_435,c_4])).

tff(c_713,plain,(
    ! [A_178,A_179,B_180] :
      ( m1_subset_1('#skF_1'(A_178,k1_relat_1(A_179),A_179),B_180)
      | ~ r2_hidden(A_178,k2_relat_1(A_179))
      | ~ v1_relat_1(A_179)
      | ~ r1_tarski(k1_relat_1(A_179),B_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_459])).

tff(c_38,plain,(
    ! [E_31] :
      ( k1_funct_1('#skF_5',E_31) != '#skF_2'
      | ~ m1_subset_1(E_31,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_765,plain,(
    ! [A_184,A_185] :
      ( k1_funct_1('#skF_5','#skF_1'(A_184,k1_relat_1(A_185),A_185)) != '#skF_2'
      | ~ r2_hidden(A_184,k2_relat_1(A_185))
      | ~ r1_tarski(k1_relat_1(A_185),'#skF_3')
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_713,c_38])).

tff(c_769,plain,(
    ! [A_120] :
      ( A_120 != '#skF_2'
      | ~ r2_hidden(A_120,k2_relat_1('#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_120,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_765])).

tff(c_771,plain,(
    ! [A_120] :
      ( A_120 != '#skF_2'
      | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
      | ~ r2_hidden(A_120,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_46,c_72,c_769])).

tff(c_772,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_799,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_772])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_129,c_799])).

tff(c_812,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_152,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_161,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_152])).

tff(c_40,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_165,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_40])).

tff(c_814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_812,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.43  
% 3.10/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.10/1.43  
% 3.10/1.43  %Foreground sorts:
% 3.10/1.43  
% 3.10/1.43  
% 3.10/1.43  %Background operators:
% 3.10/1.43  
% 3.10/1.43  
% 3.10/1.43  %Foreground operators:
% 3.10/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.10/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.10/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.10/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.43  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.10/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.43  
% 3.10/1.45  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.10/1.45  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.10/1.45  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.45  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.10/1.45  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.10/1.45  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.10/1.45  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.10/1.45  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.10/1.45  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.10/1.45  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.10/1.45  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.45  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.45  tff(c_63, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.10/1.45  tff(c_72, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_63])).
% 3.10/1.45  tff(c_120, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.45  tff(c_129, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_120])).
% 3.10/1.45  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.10/1.45  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.45  tff(c_22, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.45  tff(c_225, plain, (![A_102, B_103, C_104]: (r2_hidden(k4_tarski('#skF_1'(A_102, B_103, C_104), A_102), C_104) | ~r2_hidden(A_102, k9_relat_1(C_104, B_103)) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.45  tff(c_26, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.45  tff(c_346, plain, (![C_119, A_120, B_121]: (k1_funct_1(C_119, '#skF_1'(A_120, B_121, C_119))=A_120 | ~v1_funct_1(C_119) | ~r2_hidden(A_120, k9_relat_1(C_119, B_121)) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_225, c_26])).
% 3.10/1.45  tff(c_357, plain, (![A_17, A_120]: (k1_funct_1(A_17, '#skF_1'(A_120, k1_relat_1(A_17), A_17))=A_120 | ~v1_funct_1(A_17) | ~r2_hidden(A_120, k2_relat_1(A_17)) | ~v1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_22, c_346])).
% 3.10/1.45  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.10/1.45  tff(c_216, plain, (![A_96, B_97, C_98]: (r2_hidden('#skF_1'(A_96, B_97, C_98), k1_relat_1(C_98)) | ~r2_hidden(A_96, k9_relat_1(C_98, B_97)) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.45  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.45  tff(c_381, plain, (![A_128, B_129, C_130, A_131]: (r2_hidden('#skF_1'(A_128, B_129, C_130), A_131) | ~m1_subset_1(k1_relat_1(C_130), k1_zfmisc_1(A_131)) | ~r2_hidden(A_128, k9_relat_1(C_130, B_129)) | ~v1_relat_1(C_130))), inference(resolution, [status(thm)], [c_216, c_2])).
% 3.10/1.45  tff(c_435, plain, (![A_138, B_139, C_140, B_141]: (r2_hidden('#skF_1'(A_138, B_139, C_140), B_141) | ~r2_hidden(A_138, k9_relat_1(C_140, B_139)) | ~v1_relat_1(C_140) | ~r1_tarski(k1_relat_1(C_140), B_141))), inference(resolution, [status(thm)], [c_8, c_381])).
% 3.10/1.45  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.10/1.45  tff(c_459, plain, (![A_144, B_145, C_146, B_147]: (m1_subset_1('#skF_1'(A_144, B_145, C_146), B_147) | ~r2_hidden(A_144, k9_relat_1(C_146, B_145)) | ~v1_relat_1(C_146) | ~r1_tarski(k1_relat_1(C_146), B_147))), inference(resolution, [status(thm)], [c_435, c_4])).
% 3.10/1.45  tff(c_713, plain, (![A_178, A_179, B_180]: (m1_subset_1('#skF_1'(A_178, k1_relat_1(A_179), A_179), B_180) | ~r2_hidden(A_178, k2_relat_1(A_179)) | ~v1_relat_1(A_179) | ~r1_tarski(k1_relat_1(A_179), B_180) | ~v1_relat_1(A_179))), inference(superposition, [status(thm), theory('equality')], [c_22, c_459])).
% 3.10/1.45  tff(c_38, plain, (![E_31]: (k1_funct_1('#skF_5', E_31)!='#skF_2' | ~m1_subset_1(E_31, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.45  tff(c_765, plain, (![A_184, A_185]: (k1_funct_1('#skF_5', '#skF_1'(A_184, k1_relat_1(A_185), A_185))!='#skF_2' | ~r2_hidden(A_184, k2_relat_1(A_185)) | ~r1_tarski(k1_relat_1(A_185), '#skF_3') | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_713, c_38])).
% 3.10/1.45  tff(c_769, plain, (![A_120]: (A_120!='#skF_2' | ~r2_hidden(A_120, k2_relat_1('#skF_5')) | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~r2_hidden(A_120, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_357, c_765])).
% 3.10/1.45  tff(c_771, plain, (![A_120]: (A_120!='#skF_2' | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~r2_hidden(A_120, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_46, c_72, c_769])).
% 3.10/1.45  tff(c_772, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_771])).
% 3.10/1.45  tff(c_799, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_772])).
% 3.10/1.45  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_129, c_799])).
% 3.10/1.45  tff(c_812, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_771])).
% 3.10/1.45  tff(c_152, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.45  tff(c_161, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_152])).
% 3.10/1.45  tff(c_40, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.45  tff(c_165, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_40])).
% 3.10/1.45  tff(c_814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_812, c_165])).
% 3.10/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.45  
% 3.10/1.45  Inference rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Ref     : 0
% 3.10/1.45  #Sup     : 167
% 3.10/1.45  #Fact    : 0
% 3.10/1.45  #Define  : 0
% 3.10/1.45  #Split   : 2
% 3.10/1.45  #Chain   : 0
% 3.10/1.45  #Close   : 0
% 3.10/1.45  
% 3.10/1.45  Ordering : KBO
% 3.10/1.45  
% 3.10/1.45  Simplification rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Subsume      : 4
% 3.10/1.45  #Demod        : 17
% 3.10/1.45  #Tautology    : 17
% 3.10/1.45  #SimpNegUnit  : 1
% 3.10/1.45  #BackRed      : 5
% 3.10/1.45  
% 3.10/1.45  #Partial instantiations: 0
% 3.10/1.45  #Strategies tried      : 1
% 3.10/1.45  
% 3.10/1.45  Timing (in seconds)
% 3.10/1.45  ----------------------
% 3.10/1.45  Preprocessing        : 0.32
% 3.10/1.45  Parsing              : 0.17
% 3.10/1.45  CNF conversion       : 0.02
% 3.10/1.45  Main loop            : 0.38
% 3.10/1.45  Inferencing          : 0.14
% 3.10/1.45  Reduction            : 0.09
% 3.10/1.45  Demodulation         : 0.07
% 3.10/1.45  BG Simplification    : 0.02
% 3.10/1.45  Subsumption          : 0.08
% 3.10/1.45  Abstraction          : 0.02
% 3.10/1.45  MUC search           : 0.00
% 3.10/1.45  Cooper               : 0.00
% 3.10/1.45  Total                : 0.73
% 3.10/1.45  Index Insertion      : 0.00
% 3.10/1.45  Index Deletion       : 0.00
% 3.10/1.45  Index Matching       : 0.00
% 3.10/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
