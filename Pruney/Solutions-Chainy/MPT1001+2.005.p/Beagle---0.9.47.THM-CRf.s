%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:56 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 115 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 230 expanded)
%              Number of equality atoms :   34 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_251,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_260,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_251])).

tff(c_38,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_67,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_261,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_67])).

tff(c_266,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k2_relset_1(A_79,B_80,C_81),k1_zfmisc_1(B_80))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_280,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_266])).

tff(c_285,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_280])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_289,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_291,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_289,c_2])).

tff(c_294,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_291])).

tff(c_69,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | r1_tarski(A_7,k2_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( k10_relat_1(B_8,k1_tarski('#skF_1'(A_7,B_8))) = k1_xboole_0
      | r1_tarski(A_7,k2_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_380,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k8_relset_1(A_102,B_103,C_104,D_105) = k10_relat_1(C_104,D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_391,plain,(
    ! [D_105] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_105) = k10_relat_1('#skF_4',D_105) ),
    inference(resolution,[status(thm)],[c_28,c_380])).

tff(c_44,plain,(
    ! [D_25] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_25)) != k1_xboole_0
      | ~ r2_hidden(D_25,'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_238,plain,(
    ! [D_25] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_25)) != k1_xboole_0
      | ~ r2_hidden(D_25,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_44])).

tff(c_402,plain,(
    ! [D_107] :
      ( k10_relat_1('#skF_4',k1_tarski(D_107)) != k1_xboole_0
      | ~ r2_hidden(D_107,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_238])).

tff(c_406,plain,(
    ! [A_7] :
      ( ~ r2_hidden('#skF_1'(A_7,'#skF_4'),'#skF_3')
      | r1_tarski(A_7,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_402])).

tff(c_410,plain,(
    ! [A_108] :
      ( ~ r2_hidden('#skF_1'(A_108,'#skF_4'),'#skF_3')
      | r1_tarski(A_108,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_406])).

tff(c_414,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_410])).

tff(c_417,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_414])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_417])).

tff(c_420,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_588,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k8_relset_1(A_139,B_140,C_141,D_142) = k10_relat_1(C_141,D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_605,plain,(
    ! [D_143] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_143) = k10_relat_1('#skF_4',D_143) ),
    inference(resolution,[status(thm)],[c_28,c_588])).

tff(c_421,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_449,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_34])).

tff(c_611,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_449])).

tff(c_426,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_435,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_426])).

tff(c_467,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_474,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_467])).

tff(c_477,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_474])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( k10_relat_1(B_6,k1_tarski(A_5)) != k1_xboole_0
      | ~ r2_hidden(A_5,k2_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_481,plain,(
    ! [A_5] :
      ( k10_relat_1('#skF_4',k1_tarski(A_5)) != k1_xboole_0
      | ~ r2_hidden(A_5,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_14])).

tff(c_488,plain,(
    ! [A_5] :
      ( k10_relat_1('#skF_4',k1_tarski(A_5)) != k1_xboole_0
      | ~ r2_hidden(A_5,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_481])).

tff(c_626,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_488])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:34:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.73/1.38  
% 2.73/1.38  %Foreground sorts:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Background operators:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Foreground operators:
% 2.73/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.73/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.38  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.73/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.73/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.38  
% 2.73/1.40  tff(f_83, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_2)).
% 2.73/1.40  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.40  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.73/1.40  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.73/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.40  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.40  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 2.73/1.40  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.73/1.40  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.73/1.40  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.40  tff(c_251, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.40  tff(c_260, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_251])).
% 2.73/1.40  tff(c_38, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.40  tff(c_67, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_38])).
% 2.73/1.40  tff(c_261, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_67])).
% 2.73/1.40  tff(c_266, plain, (![A_79, B_80, C_81]: (m1_subset_1(k2_relset_1(A_79, B_80, C_81), k1_zfmisc_1(B_80)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.40  tff(c_280, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_260, c_266])).
% 2.73/1.40  tff(c_285, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_280])).
% 2.73/1.40  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.40  tff(c_289, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_285, c_8])).
% 2.73/1.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.40  tff(c_291, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_289, c_2])).
% 2.73/1.40  tff(c_294, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_261, c_291])).
% 2.73/1.40  tff(c_69, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.40  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_69])).
% 2.73/1.40  tff(c_18, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | r1_tarski(A_7, k2_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.40  tff(c_16, plain, (![B_8, A_7]: (k10_relat_1(B_8, k1_tarski('#skF_1'(A_7, B_8)))=k1_xboole_0 | r1_tarski(A_7, k2_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.40  tff(c_380, plain, (![A_102, B_103, C_104, D_105]: (k8_relset_1(A_102, B_103, C_104, D_105)=k10_relat_1(C_104, D_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.73/1.40  tff(c_391, plain, (![D_105]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_105)=k10_relat_1('#skF_4', D_105))), inference(resolution, [status(thm)], [c_28, c_380])).
% 2.73/1.40  tff(c_44, plain, (![D_25]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_25))!=k1_xboole_0 | ~r2_hidden(D_25, '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.40  tff(c_238, plain, (![D_25]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_25))!=k1_xboole_0 | ~r2_hidden(D_25, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_67, c_44])).
% 2.73/1.40  tff(c_402, plain, (![D_107]: (k10_relat_1('#skF_4', k1_tarski(D_107))!=k1_xboole_0 | ~r2_hidden(D_107, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_391, c_238])).
% 2.73/1.40  tff(c_406, plain, (![A_7]: (~r2_hidden('#skF_1'(A_7, '#skF_4'), '#skF_3') | r1_tarski(A_7, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_402])).
% 2.73/1.40  tff(c_410, plain, (![A_108]: (~r2_hidden('#skF_1'(A_108, '#skF_4'), '#skF_3') | r1_tarski(A_108, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_406])).
% 2.73/1.40  tff(c_414, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_410])).
% 2.73/1.40  tff(c_417, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_414])).
% 2.73/1.40  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_294, c_417])).
% 2.73/1.40  tff(c_420, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.73/1.40  tff(c_588, plain, (![A_139, B_140, C_141, D_142]: (k8_relset_1(A_139, B_140, C_141, D_142)=k10_relat_1(C_141, D_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.73/1.40  tff(c_605, plain, (![D_143]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_143)=k10_relat_1('#skF_4', D_143))), inference(resolution, [status(thm)], [c_28, c_588])).
% 2.73/1.40  tff(c_421, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.73/1.40  tff(c_34, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.40  tff(c_449, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_421, c_34])).
% 2.73/1.40  tff(c_611, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_605, c_449])).
% 2.73/1.40  tff(c_426, plain, (![C_109, A_110, B_111]: (v1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.40  tff(c_435, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_426])).
% 2.73/1.40  tff(c_467, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.40  tff(c_474, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_467])).
% 2.73/1.40  tff(c_477, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_421, c_474])).
% 2.73/1.40  tff(c_14, plain, (![B_6, A_5]: (k10_relat_1(B_6, k1_tarski(A_5))!=k1_xboole_0 | ~r2_hidden(A_5, k2_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.73/1.40  tff(c_481, plain, (![A_5]: (k10_relat_1('#skF_4', k1_tarski(A_5))!=k1_xboole_0 | ~r2_hidden(A_5, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_14])).
% 2.73/1.40  tff(c_488, plain, (![A_5]: (k10_relat_1('#skF_4', k1_tarski(A_5))!=k1_xboole_0 | ~r2_hidden(A_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_481])).
% 2.73/1.40  tff(c_626, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_611, c_488])).
% 2.73/1.40  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_420, c_626])).
% 2.73/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  Inference rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Ref     : 0
% 2.73/1.40  #Sup     : 121
% 2.73/1.40  #Fact    : 0
% 2.73/1.40  #Define  : 0
% 2.73/1.40  #Split   : 5
% 2.73/1.40  #Chain   : 0
% 2.73/1.40  #Close   : 0
% 2.73/1.40  
% 2.73/1.40  Ordering : KBO
% 2.73/1.40  
% 2.73/1.40  Simplification rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Subsume      : 3
% 2.73/1.40  #Demod        : 45
% 2.73/1.40  #Tautology    : 53
% 2.73/1.40  #SimpNegUnit  : 6
% 2.73/1.40  #BackRed      : 4
% 2.73/1.40  
% 2.73/1.40  #Partial instantiations: 0
% 2.73/1.40  #Strategies tried      : 1
% 2.73/1.40  
% 2.73/1.40  Timing (in seconds)
% 2.73/1.40  ----------------------
% 2.73/1.40  Preprocessing        : 0.33
% 2.73/1.40  Parsing              : 0.17
% 2.73/1.40  CNF conversion       : 0.02
% 2.73/1.40  Main loop            : 0.32
% 2.73/1.40  Inferencing          : 0.13
% 2.73/1.40  Reduction            : 0.09
% 2.73/1.40  Demodulation         : 0.06
% 2.73/1.40  BG Simplification    : 0.02
% 2.73/1.40  Subsumption          : 0.05
% 2.73/1.40  Abstraction          : 0.02
% 2.73/1.40  MUC search           : 0.00
% 2.73/1.40  Cooper               : 0.00
% 2.73/1.40  Total                : 0.68
% 2.73/1.40  Index Insertion      : 0.00
% 2.73/1.40  Index Deletion       : 0.00
% 2.73/1.40  Index Matching       : 0.00
% 2.73/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
