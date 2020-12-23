%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:41 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  105 (1103 expanded)
%              Number of leaves         :   36 ( 406 expanded)
%              Depth                    :   33
%              Number of atoms          :  234 (3067 expanded)
%              Number of equality atoms :  104 (1088 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
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

tff(c_58,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_62,plain,(
    v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_116,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_120,plain,(
    k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_181,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_184,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7')
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_181])).

tff(c_187,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_120,c_184])).

tff(c_188,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_187])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_4])).

tff(c_106,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_110,plain,(
    k2_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_106])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') != k1_tarski(k1_funct_1('#skF_9','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_111,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_7')) != k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_56])).

tff(c_20,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_97,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_64,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_334,plain,(
    ! [A_117,B_118] :
      ( k1_funct_1(A_117,'#skF_4'(A_117,B_118)) = '#skF_3'(A_117,B_118)
      | r2_hidden('#skF_5'(A_117,B_118),B_118)
      | k2_relat_1(A_117) = B_118
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1395,plain,(
    ! [A_165,A_166] :
      ( '#skF_5'(A_165,k1_tarski(A_166)) = A_166
      | k1_funct_1(A_165,'#skF_4'(A_165,k1_tarski(A_166))) = '#skF_3'(A_165,k1_tarski(A_166))
      | k2_relat_1(A_165) = k1_tarski(A_166)
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_215,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_4'(A_112,B_113),k1_relat_1(A_112))
      | r2_hidden('#skF_5'(A_112,B_113),B_113)
      | k2_relat_1(A_112) = B_113
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1139,plain,(
    ! [A_158,A_159] :
      ( '#skF_5'(A_158,k1_tarski(A_159)) = A_159
      | r2_hidden('#skF_4'(A_158,k1_tarski(A_159)),k1_relat_1(A_158))
      | k2_relat_1(A_158) = k1_tarski(A_159)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(resolution,[status(thm)],[c_215,c_2])).

tff(c_22,plain,(
    ! [A_14,D_53] :
      ( r2_hidden(k1_funct_1(A_14,D_53),k2_relat_1(A_14))
      | ~ r2_hidden(D_53,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_14,C_50] :
      ( r2_hidden('#skF_6'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_221,plain,(
    ! [C_114] :
      ( C_114 = '#skF_7'
      | ~ r2_hidden(C_114,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_236,plain,(
    ! [C_50] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_50) = '#skF_7'
      | ~ r2_hidden(C_50,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_26,c_221])).

tff(c_294,plain,(
    ! [C_115] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_115) = '#skF_7'
      | ~ r2_hidden(C_115,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_236])).

tff(c_302,plain,(
    ! [D_53] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_53)) = '#skF_7'
      | ~ r2_hidden(D_53,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_294])).

tff(c_361,plain,(
    ! [D_119] :
      ( '#skF_6'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_119)) = '#skF_7'
      | ~ r2_hidden(D_119,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_302])).

tff(c_24,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_6'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_367,plain,(
    ! [D_119] :
      ( k1_funct_1('#skF_9',D_119) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_119),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_119,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_24])).

tff(c_601,plain,(
    ! [D_132] :
      ( k1_funct_1('#skF_9',D_132) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_132),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_132,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_367])).

tff(c_611,plain,(
    ! [D_53] :
      ( k1_funct_1('#skF_9',D_53) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_53,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_601])).

tff(c_616,plain,(
    ! [D_53] :
      ( k1_funct_1('#skF_9',D_53) = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_53,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_611])).

tff(c_1147,plain,(
    ! [A_159] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',k1_tarski(A_159))) = k1_funct_1('#skF_9','#skF_7')
      | '#skF_5'('#skF_9',k1_tarski(A_159)) = A_159
      | k2_relat_1('#skF_9') = k1_tarski(A_159)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1139,c_616])).

tff(c_1160,plain,(
    ! [A_159] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',k1_tarski(A_159))) = k1_funct_1('#skF_9','#skF_7')
      | '#skF_5'('#skF_9',k1_tarski(A_159)) = A_159
      | k2_relat_1('#skF_9') = k1_tarski(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_1147])).

tff(c_1402,plain,(
    ! [A_166] :
      ( '#skF_3'('#skF_9',k1_tarski(A_166)) = k1_funct_1('#skF_9','#skF_7')
      | '#skF_5'('#skF_9',k1_tarski(A_166)) = A_166
      | k2_relat_1('#skF_9') = k1_tarski(A_166)
      | '#skF_5'('#skF_9',k1_tarski(A_166)) = A_166
      | k2_relat_1('#skF_9') = k1_tarski(A_166)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_1160])).

tff(c_1492,plain,(
    ! [A_168] :
      ( '#skF_3'('#skF_9',k1_tarski(A_168)) = k1_funct_1('#skF_9','#skF_7')
      | '#skF_5'('#skF_9',k1_tarski(A_168)) = A_168
      | k2_relat_1('#skF_9') = k1_tarski(A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_1402])).

tff(c_34,plain,(
    ! [A_14,B_36] :
      ( ~ r2_hidden('#skF_3'(A_14,B_36),B_36)
      | r2_hidden('#skF_5'(A_14,B_36),B_36)
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1503,plain,(
    ! [A_168] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_tarski(A_168))
      | r2_hidden('#skF_5'('#skF_9',k1_tarski(A_168)),k1_tarski(A_168))
      | k2_relat_1('#skF_9') = k1_tarski(A_168)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | '#skF_5'('#skF_9',k1_tarski(A_168)) = A_168
      | k2_relat_1('#skF_9') = k1_tarski(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1492,c_34])).

tff(c_2241,plain,(
    ! [A_194] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_tarski(A_194))
      | r2_hidden('#skF_5'('#skF_9',k1_tarski(A_194)),k1_tarski(A_194))
      | '#skF_5'('#skF_9',k1_tarski(A_194)) = A_194
      | k2_relat_1('#skF_9') = k1_tarski(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_1503])).

tff(c_2275,plain,(
    ! [A_198] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_tarski(A_198))
      | '#skF_5'('#skF_9',k1_tarski(A_198)) = A_198
      | k2_relat_1('#skF_9') = k1_tarski(A_198) ) ),
    inference(resolution,[status(thm)],[c_2241,c_2])).

tff(c_2282,plain,
    ( '#skF_5'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))) = k1_funct_1('#skF_9','#skF_7')
    | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_2275])).

tff(c_2287,plain,(
    '#skF_5'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))) = k1_funct_1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2282])).

tff(c_32,plain,(
    ! [A_14,B_36,D_49] :
      ( r2_hidden('#skF_4'(A_14,B_36),k1_relat_1(A_14))
      | k1_funct_1(A_14,D_49) != '#skF_5'(A_14,B_36)
      | ~ r2_hidden(D_49,k1_relat_1(A_14))
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2311,plain,(
    ! [D_49] :
      ( r2_hidden('#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))),k1_relat_1('#skF_9'))
      | k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2287,c_32])).

tff(c_2353,plain,(
    ! [D_49] :
      ( r2_hidden('#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))),k1_relat_1('#skF_9'))
      | k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_2311])).

tff(c_2354,plain,(
    ! [D_49] :
      ( r2_hidden('#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))),k1_relat_1('#skF_9'))
      | k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2353])).

tff(c_2372,plain,(
    ! [D_199] :
      ( k1_funct_1('#skF_9',D_199) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_199,k1_relat_1('#skF_9')) ) ),
    inference(splitLeft,[status(thm)],[c_2354])).

tff(c_2503,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_208,c_2372])).

tff(c_2504,plain,(
    r2_hidden('#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2354])).

tff(c_205,plain,(
    ! [C_5] :
      ( C_5 = '#skF_7'
      | ~ r2_hidden(C_5,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_2524,plain,(
    '#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2504,c_205])).

tff(c_30,plain,(
    ! [A_14,B_36,D_49] :
      ( k1_funct_1(A_14,'#skF_4'(A_14,B_36)) = '#skF_3'(A_14,B_36)
      | k1_funct_1(A_14,D_49) != '#skF_5'(A_14,B_36)
      | ~ r2_hidden(D_49,k1_relat_1(A_14))
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2306,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7')))) = '#skF_3'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7')))
      | k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2287,c_30])).

tff(c_2348,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7')))) = '#skF_3'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7')))
      | k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_2306])).

tff(c_2349,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7')))) = '#skF_3'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7')))
      | k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2348])).

tff(c_2638,plain,(
    ! [D_49] :
      ( '#skF_3'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))) = k1_funct_1('#skF_9','#skF_7')
      | k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2349])).

tff(c_2640,plain,(
    ! [D_205] :
      ( k1_funct_1('#skF_9',D_205) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_205,k1_relat_1('#skF_9')) ) ),
    inference(splitLeft,[status(thm)],[c_2638])).

tff(c_2771,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_208,c_2640])).

tff(c_2772,plain,(
    '#skF_3'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7'))) = k1_funct_1('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2638])).

tff(c_28,plain,(
    ! [A_14,B_36,D_49] :
      ( ~ r2_hidden('#skF_3'(A_14,B_36),B_36)
      | k1_funct_1(A_14,D_49) != '#skF_5'(A_14,B_36)
      | ~ r2_hidden(D_49,k1_relat_1(A_14))
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2788,plain,(
    ! [D_49] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_tarski(k1_funct_1('#skF_9','#skF_7')))
      | k1_funct_1('#skF_9',D_49) != '#skF_5'('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_7')))
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2772,c_28])).

tff(c_2808,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_9',D_49) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | k1_tarski(k1_funct_1('#skF_9','#skF_7')) = k2_relat_1('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_2287,c_4,c_2788])).

tff(c_2817,plain,(
    ! [D_206] :
      ( k1_funct_1('#skF_9',D_206) != k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_206,k1_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2808])).

tff(c_2948,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_208,c_2817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.84  
% 4.63/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.85  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.63/1.85  
% 4.63/1.85  %Foreground sorts:
% 4.63/1.85  
% 4.63/1.85  
% 4.63/1.85  %Background operators:
% 4.63/1.85  
% 4.63/1.85  
% 4.63/1.85  %Foreground operators:
% 4.63/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.63/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.63/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.63/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.63/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.63/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.63/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.63/1.85  tff('#skF_9', type, '#skF_9': $i).
% 4.63/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.63/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.63/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.63/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.63/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.63/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.63/1.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.63/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.63/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.63/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.85  
% 4.63/1.87  tff(f_98, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 4.63/1.87  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.63/1.87  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.63/1.87  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.63/1.87  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.63/1.87  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.63/1.87  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.63/1.87  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.63/1.87  tff(c_58, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.87  tff(c_62, plain, (v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.87  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.87  tff(c_116, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.63/1.87  tff(c_120, plain, (k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_116])).
% 4.63/1.87  tff(c_181, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.63/1.87  tff(c_184, plain, (k1_xboole_0='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7') | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_60, c_181])).
% 4.63/1.87  tff(c_187, plain, (k1_xboole_0='#skF_8' | k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_120, c_184])).
% 4.63/1.87  tff(c_188, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_58, c_187])).
% 4.63/1.87  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.87  tff(c_208, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_4])).
% 4.63/1.87  tff(c_106, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.63/1.87  tff(c_110, plain, (k2_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_106])).
% 4.63/1.87  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')!=k1_tarski(k1_funct_1('#skF_9', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.87  tff(c_111, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_7'))!=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_56])).
% 4.63/1.87  tff(c_20, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.63/1.87  tff(c_91, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.87  tff(c_94, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_91])).
% 4.63/1.87  tff(c_97, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_94])).
% 4.63/1.87  tff(c_64, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.87  tff(c_334, plain, (![A_117, B_118]: (k1_funct_1(A_117, '#skF_4'(A_117, B_118))='#skF_3'(A_117, B_118) | r2_hidden('#skF_5'(A_117, B_118), B_118) | k2_relat_1(A_117)=B_118 | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.87  tff(c_1395, plain, (![A_165, A_166]: ('#skF_5'(A_165, k1_tarski(A_166))=A_166 | k1_funct_1(A_165, '#skF_4'(A_165, k1_tarski(A_166)))='#skF_3'(A_165, k1_tarski(A_166)) | k2_relat_1(A_165)=k1_tarski(A_166) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_334, c_2])).
% 4.63/1.87  tff(c_215, plain, (![A_112, B_113]: (r2_hidden('#skF_4'(A_112, B_113), k1_relat_1(A_112)) | r2_hidden('#skF_5'(A_112, B_113), B_113) | k2_relat_1(A_112)=B_113 | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_1139, plain, (![A_158, A_159]: ('#skF_5'(A_158, k1_tarski(A_159))=A_159 | r2_hidden('#skF_4'(A_158, k1_tarski(A_159)), k1_relat_1(A_158)) | k2_relat_1(A_158)=k1_tarski(A_159) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(resolution, [status(thm)], [c_215, c_2])).
% 4.63/1.87  tff(c_22, plain, (![A_14, D_53]: (r2_hidden(k1_funct_1(A_14, D_53), k2_relat_1(A_14)) | ~r2_hidden(D_53, k1_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_26, plain, (![A_14, C_50]: (r2_hidden('#skF_6'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_221, plain, (![C_114]: (C_114='#skF_7' | ~r2_hidden(C_114, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 4.63/1.87  tff(c_236, plain, (![C_50]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_50)='#skF_7' | ~r2_hidden(C_50, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_26, c_221])).
% 4.63/1.87  tff(c_294, plain, (![C_115]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_115)='#skF_7' | ~r2_hidden(C_115, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_236])).
% 4.63/1.87  tff(c_302, plain, (![D_53]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_53))='#skF_7' | ~r2_hidden(D_53, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_22, c_294])).
% 4.63/1.87  tff(c_361, plain, (![D_119]: ('#skF_6'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_119))='#skF_7' | ~r2_hidden(D_119, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_302])).
% 4.63/1.87  tff(c_24, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_6'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_367, plain, (![D_119]: (k1_funct_1('#skF_9', D_119)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_9', D_119), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_119, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_361, c_24])).
% 4.63/1.87  tff(c_601, plain, (![D_132]: (k1_funct_1('#skF_9', D_132)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_9', D_132), k2_relat_1('#skF_9')) | ~r2_hidden(D_132, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_367])).
% 4.63/1.87  tff(c_611, plain, (![D_53]: (k1_funct_1('#skF_9', D_53)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_53, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_22, c_601])).
% 4.63/1.87  tff(c_616, plain, (![D_53]: (k1_funct_1('#skF_9', D_53)=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_53, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_611])).
% 4.63/1.87  tff(c_1147, plain, (![A_159]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', k1_tarski(A_159)))=k1_funct_1('#skF_9', '#skF_7') | '#skF_5'('#skF_9', k1_tarski(A_159))=A_159 | k2_relat_1('#skF_9')=k1_tarski(A_159) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1139, c_616])).
% 4.63/1.87  tff(c_1160, plain, (![A_159]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', k1_tarski(A_159)))=k1_funct_1('#skF_9', '#skF_7') | '#skF_5'('#skF_9', k1_tarski(A_159))=A_159 | k2_relat_1('#skF_9')=k1_tarski(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_1147])).
% 4.63/1.87  tff(c_1402, plain, (![A_166]: ('#skF_3'('#skF_9', k1_tarski(A_166))=k1_funct_1('#skF_9', '#skF_7') | '#skF_5'('#skF_9', k1_tarski(A_166))=A_166 | k2_relat_1('#skF_9')=k1_tarski(A_166) | '#skF_5'('#skF_9', k1_tarski(A_166))=A_166 | k2_relat_1('#skF_9')=k1_tarski(A_166) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1395, c_1160])).
% 4.63/1.87  tff(c_1492, plain, (![A_168]: ('#skF_3'('#skF_9', k1_tarski(A_168))=k1_funct_1('#skF_9', '#skF_7') | '#skF_5'('#skF_9', k1_tarski(A_168))=A_168 | k2_relat_1('#skF_9')=k1_tarski(A_168))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_1402])).
% 4.63/1.87  tff(c_34, plain, (![A_14, B_36]: (~r2_hidden('#skF_3'(A_14, B_36), B_36) | r2_hidden('#skF_5'(A_14, B_36), B_36) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_1503, plain, (![A_168]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_tarski(A_168)) | r2_hidden('#skF_5'('#skF_9', k1_tarski(A_168)), k1_tarski(A_168)) | k2_relat_1('#skF_9')=k1_tarski(A_168) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | '#skF_5'('#skF_9', k1_tarski(A_168))=A_168 | k2_relat_1('#skF_9')=k1_tarski(A_168))), inference(superposition, [status(thm), theory('equality')], [c_1492, c_34])).
% 4.63/1.87  tff(c_2241, plain, (![A_194]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_tarski(A_194)) | r2_hidden('#skF_5'('#skF_9', k1_tarski(A_194)), k1_tarski(A_194)) | '#skF_5'('#skF_9', k1_tarski(A_194))=A_194 | k2_relat_1('#skF_9')=k1_tarski(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_1503])).
% 4.63/1.87  tff(c_2275, plain, (![A_198]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_tarski(A_198)) | '#skF_5'('#skF_9', k1_tarski(A_198))=A_198 | k2_relat_1('#skF_9')=k1_tarski(A_198))), inference(resolution, [status(thm)], [c_2241, c_2])).
% 4.63/1.87  tff(c_2282, plain, ('#skF_5'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7')))=k1_funct_1('#skF_9', '#skF_7') | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_4, c_2275])).
% 4.63/1.87  tff(c_2287, plain, ('#skF_5'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7')))=k1_funct_1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_111, c_2282])).
% 4.63/1.87  tff(c_32, plain, (![A_14, B_36, D_49]: (r2_hidden('#skF_4'(A_14, B_36), k1_relat_1(A_14)) | k1_funct_1(A_14, D_49)!='#skF_5'(A_14, B_36) | ~r2_hidden(D_49, k1_relat_1(A_14)) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_2311, plain, (![D_49]: (r2_hidden('#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))), k1_relat_1('#skF_9')) | k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2287, c_32])).
% 4.63/1.87  tff(c_2353, plain, (![D_49]: (r2_hidden('#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))), k1_relat_1('#skF_9')) | k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_2311])).
% 4.63/1.87  tff(c_2354, plain, (![D_49]: (r2_hidden('#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))), k1_relat_1('#skF_9')) | k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_111, c_2353])).
% 4.63/1.87  tff(c_2372, plain, (![D_199]: (k1_funct_1('#skF_9', D_199)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_199, k1_relat_1('#skF_9')))), inference(splitLeft, [status(thm)], [c_2354])).
% 4.63/1.87  tff(c_2503, plain, $false, inference(resolution, [status(thm)], [c_208, c_2372])).
% 4.63/1.87  tff(c_2504, plain, (r2_hidden('#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))), k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_2354])).
% 4.63/1.87  tff(c_205, plain, (![C_5]: (C_5='#skF_7' | ~r2_hidden(C_5, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 4.63/1.87  tff(c_2524, plain, ('#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7')))='#skF_7'), inference(resolution, [status(thm)], [c_2504, c_205])).
% 4.63/1.87  tff(c_30, plain, (![A_14, B_36, D_49]: (k1_funct_1(A_14, '#skF_4'(A_14, B_36))='#skF_3'(A_14, B_36) | k1_funct_1(A_14, D_49)!='#skF_5'(A_14, B_36) | ~r2_hidden(D_49, k1_relat_1(A_14)) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_2306, plain, (![D_49]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))))='#skF_3'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))) | k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2287, c_30])).
% 4.63/1.87  tff(c_2348, plain, (![D_49]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))))='#skF_3'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))) | k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_2306])).
% 4.63/1.87  tff(c_2349, plain, (![D_49]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))))='#skF_3'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))) | k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_111, c_2348])).
% 4.63/1.87  tff(c_2638, plain, (![D_49]: ('#skF_3'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7')))=k1_funct_1('#skF_9', '#skF_7') | k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2349])).
% 4.63/1.87  tff(c_2640, plain, (![D_205]: (k1_funct_1('#skF_9', D_205)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_205, k1_relat_1('#skF_9')))), inference(splitLeft, [status(thm)], [c_2638])).
% 4.63/1.87  tff(c_2771, plain, $false, inference(resolution, [status(thm)], [c_208, c_2640])).
% 4.63/1.87  tff(c_2772, plain, ('#skF_3'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7')))=k1_funct_1('#skF_9', '#skF_7')), inference(splitRight, [status(thm)], [c_2638])).
% 4.63/1.87  tff(c_28, plain, (![A_14, B_36, D_49]: (~r2_hidden('#skF_3'(A_14, B_36), B_36) | k1_funct_1(A_14, D_49)!='#skF_5'(A_14, B_36) | ~r2_hidden(D_49, k1_relat_1(A_14)) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.87  tff(c_2788, plain, (![D_49]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_tarski(k1_funct_1('#skF_9', '#skF_7'))) | k1_funct_1('#skF_9', D_49)!='#skF_5'('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_7'))) | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2772, c_28])).
% 4.63/1.87  tff(c_2808, plain, (![D_49]: (k1_funct_1('#skF_9', D_49)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | k1_tarski(k1_funct_1('#skF_9', '#skF_7'))=k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_2287, c_4, c_2788])).
% 4.63/1.87  tff(c_2817, plain, (![D_206]: (k1_funct_1('#skF_9', D_206)!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden(D_206, k1_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_111, c_2808])).
% 4.63/1.87  tff(c_2948, plain, $false, inference(resolution, [status(thm)], [c_208, c_2817])).
% 4.63/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.87  
% 4.63/1.87  Inference rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Ref     : 2
% 4.63/1.87  #Sup     : 501
% 4.63/1.87  #Fact    : 4
% 4.63/1.87  #Define  : 0
% 4.63/1.87  #Split   : 7
% 4.63/1.87  #Chain   : 0
% 4.63/1.87  #Close   : 0
% 4.63/1.87  
% 4.63/1.87  Ordering : KBO
% 4.63/1.87  
% 4.63/1.87  Simplification rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Subsume      : 83
% 4.63/1.87  #Demod        : 621
% 4.63/1.87  #Tautology    : 243
% 4.63/1.87  #SimpNegUnit  : 134
% 4.63/1.87  #BackRed      : 13
% 4.63/1.87  
% 4.63/1.87  #Partial instantiations: 0
% 4.63/1.87  #Strategies tried      : 1
% 4.63/1.87  
% 4.63/1.87  Timing (in seconds)
% 4.63/1.87  ----------------------
% 4.63/1.87  Preprocessing        : 0.36
% 4.63/1.87  Parsing              : 0.18
% 4.63/1.87  CNF conversion       : 0.03
% 4.63/1.87  Main loop            : 0.73
% 4.63/1.87  Inferencing          : 0.26
% 4.63/1.87  Reduction            : 0.25
% 4.63/1.87  Demodulation         : 0.16
% 4.63/1.87  BG Simplification    : 0.04
% 4.63/1.87  Subsumption          : 0.13
% 4.63/1.87  Abstraction          : 0.04
% 4.63/1.87  MUC search           : 0.00
% 4.63/1.87  Cooper               : 0.00
% 4.63/1.87  Total                : 1.13
% 4.63/1.87  Index Insertion      : 0.00
% 4.63/1.87  Index Deletion       : 0.00
% 4.63/1.87  Index Matching       : 0.00
% 4.63/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
