%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:10 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 109 expanded)
%              Number of leaves         :   40 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 209 expanded)
%              Number of equality atoms :   52 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_133,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_137,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_133])).

tff(c_74,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_126,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_130,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_126])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_199,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_203,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_199])).

tff(c_385,plain,(
    ! [B_152,A_153,C_154] :
      ( k1_xboole_0 = B_152
      | k1_relset_1(A_153,B_152,C_154) = A_153
      | ~ v1_funct_2(C_154,A_153,B_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_388,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_385])).

tff(c_391,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_203,c_388])).

tff(c_392,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_353,plain,(
    ! [B_147,C_148,A_149] :
      ( r2_hidden(k1_funct_1(B_147,C_148),A_149)
      | ~ r2_hidden(C_148,k1_relat_1(B_147))
      | ~ v1_funct_1(B_147)
      | ~ v5_relat_1(B_147,A_149)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_268,plain,(
    ! [D_133,F_132,B_130,A_129,C_131] :
      ( F_132 = D_133
      | F_132 = C_131
      | F_132 = B_130
      | F_132 = A_129
      | ~ r2_hidden(F_132,k2_enumset1(A_129,B_130,C_131,D_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_297,plain,(
    ! [F_134,C_135,B_136,A_137] :
      ( F_134 = C_135
      | F_134 = B_136
      | F_134 = A_137
      | F_134 = A_137
      | ~ r2_hidden(F_134,k1_enumset1(A_137,B_136,C_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_268])).

tff(c_321,plain,(
    ! [F_138,B_139,A_140] :
      ( F_138 = B_139
      | F_138 = A_140
      | F_138 = A_140
      | F_138 = A_140
      | ~ r2_hidden(F_138,k2_tarski(A_140,B_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_297])).

tff(c_334,plain,(
    ! [F_138,A_2] :
      ( F_138 = A_2
      | F_138 = A_2
      | F_138 = A_2
      | F_138 = A_2
      | ~ r2_hidden(F_138,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_321])).

tff(c_511,plain,(
    ! [B_167,C_168,A_169] :
      ( k1_funct_1(B_167,C_168) = A_169
      | ~ r2_hidden(C_168,k1_relat_1(B_167))
      | ~ v1_funct_1(B_167)
      | ~ v5_relat_1(B_167,k1_tarski(A_169))
      | ~ v1_relat_1(B_167) ) ),
    inference(resolution,[status(thm)],[c_353,c_334])).

tff(c_513,plain,(
    ! [C_168,A_169] :
      ( k1_funct_1('#skF_6',C_168) = A_169
      | ~ r2_hidden(C_168,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_169))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_511])).

tff(c_527,plain,(
    ! [C_170,A_171] :
      ( k1_funct_1('#skF_6',C_170) = A_171
      | ~ r2_hidden(C_170,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_80,c_513])).

tff(c_542,plain,(
    ! [A_172] :
      ( k1_funct_1('#skF_6','#skF_5') = A_172
      | ~ v5_relat_1('#skF_6',k1_tarski(A_172)) ) ),
    inference(resolution,[status(thm)],[c_74,c_527])).

tff(c_545,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_137,c_542])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_545])).

tff(c_550,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_139,plain,(
    ! [A_83,B_84,C_85] : k2_enumset1(A_83,A_83,B_84,C_85) = k1_enumset1(A_83,B_84,C_85) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [F_15,A_8,C_10,D_11] : r2_hidden(F_15,k2_enumset1(A_8,F_15,C_10,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,(
    ! [A_86,B_87,C_88] : r2_hidden(A_86,k1_enumset1(A_86,B_87,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_16])).

tff(c_180,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_172])).

tff(c_193,plain,(
    ! [A_94] : r2_hidden(A_94,k1_tarski(A_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_180])).

tff(c_50,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_197,plain,(
    ! [A_94] : ~ r1_tarski(k1_tarski(A_94),A_94) ),
    inference(resolution,[status(thm)],[c_193,c_50])).

tff(c_562,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_197])).

tff(c_570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 09:28:51 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.45  
% 2.76/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 3.06/1.45  
% 3.06/1.45  %Foreground sorts:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Background operators:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Foreground operators:
% 3.06/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.06/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.06/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.06/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.45  
% 3.12/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.12/1.46  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.12/1.46  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.12/1.46  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.12/1.46  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.12/1.46  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.12/1.46  tff(f_80, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.12/1.46  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.12/1.46  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.12/1.46  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.12/1.46  tff(f_51, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 3.12/1.46  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.12/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.46  tff(c_72, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.46  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.46  tff(c_133, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.12/1.46  tff(c_137, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_133])).
% 3.12/1.46  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.46  tff(c_126, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.12/1.46  tff(c_130, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_126])).
% 3.12/1.46  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.46  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.46  tff(c_199, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.46  tff(c_203, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_199])).
% 3.12/1.46  tff(c_385, plain, (![B_152, A_153, C_154]: (k1_xboole_0=B_152 | k1_relset_1(A_153, B_152, C_154)=A_153 | ~v1_funct_2(C_154, A_153, B_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.12/1.46  tff(c_388, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_385])).
% 3.12/1.46  tff(c_391, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_203, c_388])).
% 3.12/1.46  tff(c_392, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_391])).
% 3.12/1.46  tff(c_353, plain, (![B_147, C_148, A_149]: (r2_hidden(k1_funct_1(B_147, C_148), A_149) | ~r2_hidden(C_148, k1_relat_1(B_147)) | ~v1_funct_1(B_147) | ~v5_relat_1(B_147, A_149) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.12/1.46  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.46  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.46  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.46  tff(c_268, plain, (![D_133, F_132, B_130, A_129, C_131]: (F_132=D_133 | F_132=C_131 | F_132=B_130 | F_132=A_129 | ~r2_hidden(F_132, k2_enumset1(A_129, B_130, C_131, D_133)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.46  tff(c_297, plain, (![F_134, C_135, B_136, A_137]: (F_134=C_135 | F_134=B_136 | F_134=A_137 | F_134=A_137 | ~r2_hidden(F_134, k1_enumset1(A_137, B_136, C_135)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_268])).
% 3.12/1.46  tff(c_321, plain, (![F_138, B_139, A_140]: (F_138=B_139 | F_138=A_140 | F_138=A_140 | F_138=A_140 | ~r2_hidden(F_138, k2_tarski(A_140, B_139)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_297])).
% 3.12/1.46  tff(c_334, plain, (![F_138, A_2]: (F_138=A_2 | F_138=A_2 | F_138=A_2 | F_138=A_2 | ~r2_hidden(F_138, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_321])).
% 3.12/1.46  tff(c_511, plain, (![B_167, C_168, A_169]: (k1_funct_1(B_167, C_168)=A_169 | ~r2_hidden(C_168, k1_relat_1(B_167)) | ~v1_funct_1(B_167) | ~v5_relat_1(B_167, k1_tarski(A_169)) | ~v1_relat_1(B_167))), inference(resolution, [status(thm)], [c_353, c_334])).
% 3.12/1.46  tff(c_513, plain, (![C_168, A_169]: (k1_funct_1('#skF_6', C_168)=A_169 | ~r2_hidden(C_168, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', k1_tarski(A_169)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_392, c_511])).
% 3.12/1.46  tff(c_527, plain, (![C_170, A_171]: (k1_funct_1('#skF_6', C_170)=A_171 | ~r2_hidden(C_170, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_171)))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_80, c_513])).
% 3.12/1.46  tff(c_542, plain, (![A_172]: (k1_funct_1('#skF_6', '#skF_5')=A_172 | ~v5_relat_1('#skF_6', k1_tarski(A_172)))), inference(resolution, [status(thm)], [c_74, c_527])).
% 3.12/1.46  tff(c_545, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_137, c_542])).
% 3.12/1.46  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_545])).
% 3.12/1.46  tff(c_550, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_391])).
% 3.12/1.46  tff(c_139, plain, (![A_83, B_84, C_85]: (k2_enumset1(A_83, A_83, B_84, C_85)=k1_enumset1(A_83, B_84, C_85))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.46  tff(c_16, plain, (![F_15, A_8, C_10, D_11]: (r2_hidden(F_15, k2_enumset1(A_8, F_15, C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.46  tff(c_172, plain, (![A_86, B_87, C_88]: (r2_hidden(A_86, k1_enumset1(A_86, B_87, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_16])).
% 3.12/1.46  tff(c_180, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_172])).
% 3.12/1.46  tff(c_193, plain, (![A_94]: (r2_hidden(A_94, k1_tarski(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_180])).
% 3.12/1.46  tff(c_50, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.12/1.46  tff(c_197, plain, (![A_94]: (~r1_tarski(k1_tarski(A_94), A_94))), inference(resolution, [status(thm)], [c_193, c_50])).
% 3.12/1.46  tff(c_562, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_197])).
% 3.12/1.46  tff(c_570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_562])).
% 3.12/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.46  
% 3.12/1.46  Inference rules
% 3.12/1.46  ----------------------
% 3.12/1.46  #Ref     : 0
% 3.12/1.46  #Sup     : 106
% 3.12/1.46  #Fact    : 0
% 3.12/1.46  #Define  : 0
% 3.12/1.46  #Split   : 3
% 3.12/1.46  #Chain   : 0
% 3.12/1.46  #Close   : 0
% 3.12/1.46  
% 3.12/1.46  Ordering : KBO
% 3.12/1.46  
% 3.12/1.46  Simplification rules
% 3.12/1.46  ----------------------
% 3.12/1.46  #Subsume      : 11
% 3.12/1.46  #Demod        : 19
% 3.12/1.46  #Tautology    : 27
% 3.12/1.46  #SimpNegUnit  : 1
% 3.12/1.46  #BackRed      : 5
% 3.12/1.46  
% 3.12/1.46  #Partial instantiations: 0
% 3.12/1.46  #Strategies tried      : 1
% 3.12/1.46  
% 3.12/1.46  Timing (in seconds)
% 3.12/1.46  ----------------------
% 3.12/1.47  Preprocessing        : 0.36
% 3.12/1.47  Parsing              : 0.18
% 3.12/1.47  CNF conversion       : 0.03
% 3.12/1.47  Main loop            : 0.32
% 3.12/1.47  Inferencing          : 0.11
% 3.12/1.47  Reduction            : 0.10
% 3.12/1.47  Demodulation         : 0.07
% 3.12/1.47  BG Simplification    : 0.02
% 3.12/1.47  Subsumption          : 0.06
% 3.12/1.47  Abstraction          : 0.02
% 3.12/1.47  MUC search           : 0.00
% 3.12/1.47  Cooper               : 0.00
% 3.12/1.47  Total                : 0.71
% 3.12/1.47  Index Insertion      : 0.00
% 3.12/1.47  Index Deletion       : 0.00
% 3.12/1.47  Index Matching       : 0.00
% 3.12/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
