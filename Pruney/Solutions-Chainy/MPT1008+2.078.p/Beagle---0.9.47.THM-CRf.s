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
% DateTime   : Thu Dec  3 10:14:36 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 838 expanded)
%              Number of leaves         :   36 ( 318 expanded)
%              Depth                    :   28
%              Number of atoms          :  177 (2382 expanded)
%              Number of equality atoms :   81 ( 794 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_106,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_110,plain,(
    k2_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_106])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') != k1_tarski(k1_funct_1('#skF_9','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_112,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_7')) != k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_56])).

tff(c_90,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_90])).

tff(c_64,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [A_12,D_51] :
      ( r2_hidden(k1_funct_1(A_12,D_51),k2_relat_1(A_12))
      | ~ r2_hidden(D_51,k1_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_12,C_48] :
      ( r2_hidden('#skF_6'(A_12,k2_relat_1(A_12),C_48),k1_relat_1(A_12))
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_117,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_121,plain,(
    k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_117])).

tff(c_178,plain,(
    ! [B_105,A_106,C_107] :
      ( k1_xboole_0 = B_105
      | k1_relset_1(A_106,B_105,C_107) = A_106
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7')
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_178])).

tff(c_184,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_121,c_181])).

tff(c_185,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_184])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_204,plain,(
    ! [C_108] :
      ( C_108 = '#skF_7'
      | ~ r2_hidden(C_108,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_2])).

tff(c_211,plain,(
    ! [C_48] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_48) = '#skF_7'
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_204])).

tff(c_259,plain,(
    ! [C_111] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_111) = '#skF_7'
      | ~ r2_hidden(C_111,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_211])).

tff(c_263,plain,(
    ! [D_51] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_51)) = '#skF_7'
      | ~ r2_hidden(D_51,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_259])).

tff(c_277,plain,(
    ! [D_112] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_112)) = '#skF_7'
      | ~ r2_hidden(D_112,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_263])).

tff(c_22,plain,(
    ! [A_12,C_48] :
      ( k1_funct_1(A_12,'#skF_6'(A_12,k2_relat_1(A_12),C_48)) = C_48
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_283,plain,(
    ! [D_112] :
      ( k1_funct_1('#skF_9',D_112) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_112),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_112,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_22])).

tff(c_385,plain,(
    ! [D_122] :
      ( k1_funct_1('#skF_9',D_122) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_122),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_122,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_283])).

tff(c_393,plain,(
    ! [D_51] :
      ( k1_funct_1('#skF_9',D_51) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_51,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_385])).

tff(c_399,plain,(
    ! [D_123] :
      ( k1_funct_1('#skF_9',D_123) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_123,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_393])).

tff(c_406,plain,(
    ! [C_48] :
      ( k1_funct_1('#skF_9','#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_48)) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_399])).

tff(c_422,plain,(
    ! [C_124] :
      ( k1_funct_1('#skF_9','#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_124)) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(C_124,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_406])).

tff(c_434,plain,(
    ! [C_124] :
      ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_124),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_124,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_20])).

tff(c_449,plain,(
    ! [C_124] :
      ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_124),k1_relat_1('#skF_9'))
      | ~ r2_hidden(C_124,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_434])).

tff(c_886,plain,(
    ! [C_143] :
      ( ~ r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_143),k1_relat_1('#skF_9'))
      | ~ r2_hidden(C_143,k2_relat_1('#skF_9')) ) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_896,plain,(
    ! [C_48] :
      ( ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_886])).

tff(c_904,plain,(
    ! [C_144] : ~ r2_hidden(C_144,k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_896])).

tff(c_924,plain,(
    ! [D_51] :
      ( ~ r2_hidden(D_51,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_904])).

tff(c_941,plain,(
    ! [D_51] : ~ r2_hidden(D_51,k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_924])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_199,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_4])).

tff(c_945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_199])).

tff(c_946,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_431,plain,(
    ! [C_124] :
      ( k1_funct_1('#skF_9','#skF_7') = C_124
      | ~ r2_hidden(C_124,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_124,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_22])).

tff(c_489,plain,(
    ! [C_127] :
      ( k1_funct_1('#skF_9','#skF_7') = C_127
      | ~ r2_hidden(C_127,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_64,c_431])).

tff(c_763,plain,(
    ! [A_135] :
      ( '#skF_2'(A_135,k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_7')
      | '#skF_1'(A_135,k2_relat_1('#skF_9')) = A_135
      | k2_relat_1('#skF_9') = k1_tarski(A_135) ) ),
    inference(resolution,[status(thm)],[c_12,c_489])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_774,plain,(
    ! [A_135] :
      ( '#skF_1'(A_135,k2_relat_1('#skF_9')) = A_135
      | k1_funct_1('#skF_9','#skF_7') != A_135
      | k2_relat_1('#skF_9') = k1_tarski(A_135)
      | '#skF_1'(A_135,k2_relat_1('#skF_9')) = A_135
      | k2_relat_1('#skF_9') = k1_tarski(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_8])).

tff(c_2239,plain,(
    ! [A_194] :
      ( k1_funct_1('#skF_9','#skF_7') != A_194
      | k2_relat_1('#skF_9') = k1_tarski(A_194)
      | '#skF_1'(A_194,k2_relat_1('#skF_9')) = A_194 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_774])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2261,plain,(
    ! [A_195] :
      ( ~ r2_hidden(A_195,k2_relat_1('#skF_9'))
      | '#skF_2'(A_195,k2_relat_1('#skF_9')) != A_195
      | k2_relat_1('#skF_9') = k1_tarski(A_195)
      | k1_funct_1('#skF_9','#skF_7') != A_195
      | k2_relat_1('#skF_9') = k1_tarski(A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2239,c_6])).

tff(c_2290,plain,
    ( '#skF_2'(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) != k1_funct_1('#skF_9','#skF_7')
    | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_946,c_2261])).

tff(c_2336,plain,(
    '#skF_2'(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) != k1_funct_1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_112,c_2290])).

tff(c_511,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_7')
      | '#skF_1'(A_1,k2_relat_1('#skF_9')) = A_1
      | k2_relat_1('#skF_9') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_489])).

tff(c_2365,plain,
    ( '#skF_1'(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_7')
    | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_2336])).

tff(c_2368,plain,(
    '#skF_1'(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_2365])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_510,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_9')),k2_relat_1('#skF_9'))
      | k2_relat_1('#skF_9') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_489])).

tff(c_2378,plain,
    ( '#skF_2'(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9'))
    | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2368,c_510])).

tff(c_2398,plain,
    ( '#skF_2'(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_7')
    | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_2378])).

tff(c_2400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_2336,c_2398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.78  
% 4.30/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.78  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.30/1.78  
% 4.30/1.78  %Foreground sorts:
% 4.30/1.78  
% 4.30/1.78  
% 4.30/1.78  %Background operators:
% 4.30/1.78  
% 4.30/1.78  
% 4.30/1.78  %Foreground operators:
% 4.30/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.30/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.30/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.30/1.78  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.30/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.30/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.30/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.30/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.30/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.30/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.30/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.30/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.30/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.30/1.78  tff('#skF_9', type, '#skF_9': $i).
% 4.30/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.30/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.30/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.30/1.78  tff('#skF_8', type, '#skF_8': $i).
% 4.30/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.30/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.30/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.30/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.30/1.78  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.30/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.30/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.30/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.30/1.78  
% 4.30/1.80  tff(f_95, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 4.30/1.80  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.30/1.80  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.30/1.80  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.30/1.80  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.30/1.80  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.30/1.80  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.30/1.80  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.30/1.80  tff(c_106, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.30/1.80  tff(c_110, plain, (k2_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_106])).
% 4.30/1.80  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')!=k1_tarski(k1_funct_1('#skF_9', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.30/1.80  tff(c_112, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_7'))!=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_56])).
% 4.30/1.80  tff(c_90, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.30/1.80  tff(c_94, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_90])).
% 4.30/1.80  tff(c_64, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.30/1.80  tff(c_20, plain, (![A_12, D_51]: (r2_hidden(k1_funct_1(A_12, D_51), k2_relat_1(A_12)) | ~r2_hidden(D_51, k1_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.80  tff(c_24, plain, (![A_12, C_48]: (r2_hidden('#skF_6'(A_12, k2_relat_1(A_12), C_48), k1_relat_1(A_12)) | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.80  tff(c_58, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.30/1.80  tff(c_62, plain, (v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.30/1.80  tff(c_117, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.80  tff(c_121, plain, (k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_117])).
% 4.30/1.80  tff(c_178, plain, (![B_105, A_106, C_107]: (k1_xboole_0=B_105 | k1_relset_1(A_106, B_105, C_107)=A_106 | ~v1_funct_2(C_107, A_106, B_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.30/1.80  tff(c_181, plain, (k1_xboole_0='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7') | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_60, c_178])).
% 4.30/1.80  tff(c_184, plain, (k1_xboole_0='#skF_8' | k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_121, c_181])).
% 4.30/1.80  tff(c_185, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_58, c_184])).
% 4.30/1.80  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.80  tff(c_204, plain, (![C_108]: (C_108='#skF_7' | ~r2_hidden(C_108, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_185, c_2])).
% 4.30/1.80  tff(c_211, plain, (![C_48]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_48)='#skF_7' | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_204])).
% 4.30/1.80  tff(c_259, plain, (![C_111]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_111)='#skF_7' | ~r2_hidden(C_111, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_211])).
% 4.30/1.80  tff(c_263, plain, (![D_51]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_51))='#skF_7' | ~r2_hidden(D_51, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_259])).
% 4.30/1.80  tff(c_277, plain, (![D_112]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_112))='#skF_7' | ~r2_hidden(D_112, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_263])).
% 4.30/1.80  tff(c_22, plain, (![A_12, C_48]: (k1_funct_1(A_12, '#skF_6'(A_12, k2_relat_1(A_12), C_48))=C_48 | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.80  tff(c_283, plain, (![D_112]: (k1_funct_1('#skF_9', D_112)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_9', D_112), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_112, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_277, c_22])).
% 4.30/1.80  tff(c_385, plain, (![D_122]: (k1_funct_1('#skF_9', D_122)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_9', D_122), k2_relat_1('#skF_9')) | ~r2_hidden(D_122, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_283])).
% 4.30/1.80  tff(c_393, plain, (![D_51]: (k1_funct_1('#skF_9', D_51)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_51, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_385])).
% 4.30/1.80  tff(c_399, plain, (![D_123]: (k1_funct_1('#skF_9', D_123)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_123, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_393])).
% 4.30/1.80  tff(c_406, plain, (![C_48]: (k1_funct_1('#skF_9', '#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_48))=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_399])).
% 4.30/1.80  tff(c_422, plain, (![C_124]: (k1_funct_1('#skF_9', '#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_124))=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(C_124, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_406])).
% 4.30/1.80  tff(c_434, plain, (![C_124]: (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9')) | ~r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_124), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_124, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_422, c_20])).
% 4.30/1.80  tff(c_449, plain, (![C_124]: (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9')) | ~r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_124), k1_relat_1('#skF_9')) | ~r2_hidden(C_124, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_434])).
% 4.30/1.80  tff(c_886, plain, (![C_143]: (~r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_143), k1_relat_1('#skF_9')) | ~r2_hidden(C_143, k2_relat_1('#skF_9')))), inference(splitLeft, [status(thm)], [c_449])).
% 4.30/1.80  tff(c_896, plain, (![C_48]: (~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_886])).
% 4.30/1.80  tff(c_904, plain, (![C_144]: (~r2_hidden(C_144, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_896])).
% 4.30/1.80  tff(c_924, plain, (![D_51]: (~r2_hidden(D_51, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_904])).
% 4.30/1.80  tff(c_941, plain, (![D_51]: (~r2_hidden(D_51, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_924])).
% 4.30/1.80  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.80  tff(c_199, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_4])).
% 4.30/1.80  tff(c_945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_941, c_199])).
% 4.30/1.80  tff(c_946, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_449])).
% 4.30/1.80  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.80  tff(c_431, plain, (![C_124]: (k1_funct_1('#skF_9', '#skF_7')=C_124 | ~r2_hidden(C_124, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_124, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_422, c_22])).
% 4.30/1.80  tff(c_489, plain, (![C_127]: (k1_funct_1('#skF_9', '#skF_7')=C_127 | ~r2_hidden(C_127, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_64, c_431])).
% 4.30/1.80  tff(c_763, plain, (![A_135]: ('#skF_2'(A_135, k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_7') | '#skF_1'(A_135, k2_relat_1('#skF_9'))=A_135 | k2_relat_1('#skF_9')=k1_tarski(A_135))), inference(resolution, [status(thm)], [c_12, c_489])).
% 4.30/1.80  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.80  tff(c_774, plain, (![A_135]: ('#skF_1'(A_135, k2_relat_1('#skF_9'))=A_135 | k1_funct_1('#skF_9', '#skF_7')!=A_135 | k2_relat_1('#skF_9')=k1_tarski(A_135) | '#skF_1'(A_135, k2_relat_1('#skF_9'))=A_135 | k2_relat_1('#skF_9')=k1_tarski(A_135))), inference(superposition, [status(thm), theory('equality')], [c_763, c_8])).
% 4.30/1.80  tff(c_2239, plain, (![A_194]: (k1_funct_1('#skF_9', '#skF_7')!=A_194 | k2_relat_1('#skF_9')=k1_tarski(A_194) | '#skF_1'(A_194, k2_relat_1('#skF_9'))=A_194)), inference(factorization, [status(thm), theory('equality')], [c_774])).
% 4.30/1.80  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.80  tff(c_2261, plain, (![A_195]: (~r2_hidden(A_195, k2_relat_1('#skF_9')) | '#skF_2'(A_195, k2_relat_1('#skF_9'))!=A_195 | k2_relat_1('#skF_9')=k1_tarski(A_195) | k1_funct_1('#skF_9', '#skF_7')!=A_195 | k2_relat_1('#skF_9')=k1_tarski(A_195))), inference(superposition, [status(thm), theory('equality')], [c_2239, c_6])).
% 4.30/1.80  tff(c_2290, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))!=k1_funct_1('#skF_9', '#skF_7') | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_946, c_2261])).
% 4.30/1.80  tff(c_2336, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))!=k1_funct_1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_112, c_112, c_2290])).
% 4.30/1.80  tff(c_511, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_7') | '#skF_1'(A_1, k2_relat_1('#skF_9'))=A_1 | k2_relat_1('#skF_9')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_489])).
% 4.30/1.80  tff(c_2365, plain, ('#skF_1'(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_7') | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_511, c_2336])).
% 4.30/1.80  tff(c_2368, plain, ('#skF_1'(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_112, c_2365])).
% 4.30/1.80  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.80  tff(c_510, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_9')), k2_relat_1('#skF_9')) | k2_relat_1('#skF_9')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_489])).
% 4.30/1.80  tff(c_2378, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9')) | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2368, c_510])).
% 4.30/1.80  tff(c_2398, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_7') | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_946, c_2378])).
% 4.30/1.80  tff(c_2400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_2336, c_2398])).
% 4.30/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.80  
% 4.30/1.80  Inference rules
% 4.30/1.80  ----------------------
% 4.30/1.80  #Ref     : 2
% 4.30/1.80  #Sup     : 413
% 4.30/1.80  #Fact    : 4
% 4.30/1.80  #Define  : 0
% 4.30/1.80  #Split   : 4
% 4.30/1.80  #Chain   : 0
% 4.30/1.80  #Close   : 0
% 4.30/1.80  
% 4.30/1.80  Ordering : KBO
% 4.30/1.80  
% 4.30/1.80  Simplification rules
% 4.30/1.80  ----------------------
% 4.30/1.80  #Subsume      : 69
% 4.30/1.80  #Demod        : 451
% 4.30/1.80  #Tautology    : 211
% 4.30/1.80  #SimpNegUnit  : 80
% 4.30/1.80  #BackRed      : 16
% 4.30/1.80  
% 4.30/1.80  #Partial instantiations: 0
% 4.30/1.80  #Strategies tried      : 1
% 4.30/1.80  
% 4.30/1.80  Timing (in seconds)
% 4.30/1.80  ----------------------
% 4.30/1.80  Preprocessing        : 0.32
% 4.30/1.80  Parsing              : 0.16
% 4.30/1.81  CNF conversion       : 0.03
% 4.30/1.81  Main loop            : 0.71
% 4.30/1.81  Inferencing          : 0.26
% 4.30/1.81  Reduction            : 0.23
% 4.30/1.81  Demodulation         : 0.15
% 4.30/1.81  BG Simplification    : 0.04
% 4.30/1.81  Subsumption          : 0.14
% 4.30/1.81  Abstraction          : 0.04
% 4.30/1.81  MUC search           : 0.00
% 4.30/1.81  Cooper               : 0.00
% 4.30/1.81  Total                : 1.07
% 4.30/1.81  Index Insertion      : 0.00
% 4.30/1.81  Index Deletion       : 0.00
% 4.30/1.81  Index Matching       : 0.00
% 4.30/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
