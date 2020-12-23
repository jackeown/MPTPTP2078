%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:23 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 151 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 246 expanded)
%              Number of equality atoms :   37 (  85 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_75,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_747,plain,(
    ! [A_147,B_148,C_149] :
      ( k2_relset_1(A_147,B_148,C_149) = k2_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_751,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_747])).

tff(c_44,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_112,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_536,plain,(
    ! [C_106,A_107,B_108,D_109] :
      ( r1_tarski(C_106,k1_relset_1(A_107,B_108,D_109))
      | ~ r1_tarski(k6_relat_1(C_106),D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_549,plain,(
    ! [A_110,B_111] :
      ( r1_tarski('#skF_2',k1_relset_1(A_110,B_111,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(resolution,[status(thm)],[c_46,c_536])).

tff(c_552,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_549])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_552])).

tff(c_557,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_766,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_557])).

tff(c_16,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_630,plain,(
    ! [B_118,A_119] :
      ( v1_relat_1(B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_119))
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_633,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_630])).

tff(c_636,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_633])).

tff(c_674,plain,(
    ! [C_133,B_134,A_135] :
      ( v5_relat_1(C_133,B_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_678,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_674])).

tff(c_839,plain,(
    ! [C_160,A_161,B_162,D_163] :
      ( r1_tarski(C_160,k2_relset_1(A_161,B_162,D_163))
      | ~ r1_tarski(k6_relat_1(C_160),D_163)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_954,plain,(
    ! [A_176,B_177] :
      ( r1_tarski('#skF_2',k2_relset_1(A_176,B_177,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(resolution,[status(thm)],[c_46,c_839])).

tff(c_957,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_954])).

tff(c_959,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_957])).

tff(c_28,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_694,plain,(
    ! [A_138,B_139] :
      ( k5_relat_1(k6_relat_1(A_138),B_139) = k7_relat_1(B_139,A_138)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [B_27,A_26] : k5_relat_1(k6_relat_1(B_27),k6_relat_1(A_26)) = k6_relat_1(k3_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_701,plain,(
    ! [A_26,A_138] :
      ( k7_relat_1(k6_relat_1(A_26),A_138) = k6_relat_1(k3_xboole_0(A_26,A_138))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_32])).

tff(c_710,plain,(
    ! [A_26,A_138] : k7_relat_1(k6_relat_1(A_26),A_138) = k6_relat_1(k3_xboole_0(A_26,A_138)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_701])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = k7_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_752,plain,(
    ! [B_150,A_151] :
      ( k2_relat_1(k5_relat_1(B_150,A_151)) = k2_relat_1(A_151)
      | ~ r1_tarski(k1_relat_1(A_151),k2_relat_1(B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_758,plain,(
    ! [B_150,A_22] :
      ( k2_relat_1(k5_relat_1(B_150,k6_relat_1(A_22))) = k2_relat_1(k6_relat_1(A_22))
      | ~ r1_tarski(A_22,k2_relat_1(B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_752])).

tff(c_771,plain,(
    ! [B_152,A_153] :
      ( k2_relat_1(k5_relat_1(B_152,k6_relat_1(A_153))) = A_153
      | ~ r1_tarski(A_153,k2_relat_1(B_152))
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_758])).

tff(c_790,plain,(
    ! [A_153,A_23] :
      ( k2_relat_1(k7_relat_1(k6_relat_1(A_153),A_23)) = A_153
      | ~ r1_tarski(A_153,k2_relat_1(k6_relat_1(A_23)))
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_771])).

tff(c_797,plain,(
    ! [A_153,A_23] :
      ( k3_xboole_0(A_153,A_23) = A_153
      | ~ r1_tarski(A_153,A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_24,c_24,c_710,c_790])).

tff(c_967,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_959,c_797])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_559,plain,(
    ! [A_112,B_113] : k1_setfam_1(k2_tarski(A_112,B_113)) = k3_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_574,plain,(
    ! [B_114,A_115] : k1_setfam_1(k2_tarski(B_114,A_115)) = k3_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_559])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_580,plain,(
    ! [B_114,A_115] : k3_xboole_0(B_114,A_115) = k3_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_8])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_804,plain,(
    ! [A_158,A_159] :
      ( k3_xboole_0(A_158,A_159) = A_158
      | ~ r1_tarski(A_158,A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_24,c_24,c_710,c_790])).

tff(c_854,plain,(
    ! [B_166,A_167] :
      ( k3_xboole_0(k2_relat_1(B_166),A_167) = k2_relat_1(B_166)
      | ~ v5_relat_1(B_166,A_167)
      | ~ v1_relat_1(B_166) ) ),
    inference(resolution,[status(thm)],[c_14,c_804])).

tff(c_880,plain,(
    ! [A_115,B_166] :
      ( k3_xboole_0(A_115,k2_relat_1(B_166)) = k2_relat_1(B_166)
      | ~ v5_relat_1(B_166,A_115)
      | ~ v1_relat_1(B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_854])).

tff(c_971,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_880])).

tff(c_978,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_678,c_971])).

tff(c_980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_766,c_978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.52  
% 3.12/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.52  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.12/1.52  
% 3.12/1.52  %Foreground sorts:
% 3.12/1.52  
% 3.12/1.52  
% 3.12/1.52  %Background operators:
% 3.12/1.52  
% 3.12/1.52  
% 3.12/1.52  %Foreground operators:
% 3.12/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.12/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.12/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.12/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.12/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.12/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.12/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.12/1.52  
% 3.21/1.54  tff(f_102, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 3.21/1.54  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.21/1.54  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 3.21/1.54  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.21/1.54  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.21/1.54  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.21/1.54  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.21/1.54  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.21/1.54  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.21/1.54  tff(f_75, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.21/1.54  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.21/1.54  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.21/1.54  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.21/1.54  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.21/1.54  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.54  tff(c_747, plain, (![A_147, B_148, C_149]: (k2_relset_1(A_147, B_148, C_149)=k2_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.21/1.54  tff(c_751, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_747])).
% 3.21/1.54  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.54  tff(c_112, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.21/1.54  tff(c_46, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.54  tff(c_536, plain, (![C_106, A_107, B_108, D_109]: (r1_tarski(C_106, k1_relset_1(A_107, B_108, D_109)) | ~r1_tarski(k6_relat_1(C_106), D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.21/1.54  tff(c_549, plain, (![A_110, B_111]: (r1_tarski('#skF_2', k1_relset_1(A_110, B_111, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(resolution, [status(thm)], [c_46, c_536])).
% 3.21/1.54  tff(c_552, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_549])).
% 3.21/1.54  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_552])).
% 3.21/1.54  tff(c_557, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.21/1.54  tff(c_766, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_751, c_557])).
% 3.21/1.54  tff(c_16, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.21/1.54  tff(c_630, plain, (![B_118, A_119]: (v1_relat_1(B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(A_119)) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.21/1.54  tff(c_633, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_630])).
% 3.21/1.54  tff(c_636, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_633])).
% 3.21/1.54  tff(c_674, plain, (![C_133, B_134, A_135]: (v5_relat_1(C_133, B_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.54  tff(c_678, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_674])).
% 3.21/1.54  tff(c_839, plain, (![C_160, A_161, B_162, D_163]: (r1_tarski(C_160, k2_relset_1(A_161, B_162, D_163)) | ~r1_tarski(k6_relat_1(C_160), D_163) | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.21/1.54  tff(c_954, plain, (![A_176, B_177]: (r1_tarski('#skF_2', k2_relset_1(A_176, B_177, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(resolution, [status(thm)], [c_46, c_839])).
% 3.21/1.54  tff(c_957, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_954])).
% 3.21/1.54  tff(c_959, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_751, c_957])).
% 3.21/1.54  tff(c_28, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.21/1.54  tff(c_24, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.54  tff(c_694, plain, (![A_138, B_139]: (k5_relat_1(k6_relat_1(A_138), B_139)=k7_relat_1(B_139, A_138) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.54  tff(c_32, plain, (![B_27, A_26]: (k5_relat_1(k6_relat_1(B_27), k6_relat_1(A_26))=k6_relat_1(k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.54  tff(c_701, plain, (![A_26, A_138]: (k7_relat_1(k6_relat_1(A_26), A_138)=k6_relat_1(k3_xboole_0(A_26, A_138)) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_694, c_32])).
% 3.21/1.54  tff(c_710, plain, (![A_26, A_138]: (k7_relat_1(k6_relat_1(A_26), A_138)=k6_relat_1(k3_xboole_0(A_26, A_138)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_701])).
% 3.21/1.54  tff(c_26, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=k7_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.54  tff(c_22, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.54  tff(c_752, plain, (![B_150, A_151]: (k2_relat_1(k5_relat_1(B_150, A_151))=k2_relat_1(A_151) | ~r1_tarski(k1_relat_1(A_151), k2_relat_1(B_150)) | ~v1_relat_1(B_150) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.21/1.54  tff(c_758, plain, (![B_150, A_22]: (k2_relat_1(k5_relat_1(B_150, k6_relat_1(A_22)))=k2_relat_1(k6_relat_1(A_22)) | ~r1_tarski(A_22, k2_relat_1(B_150)) | ~v1_relat_1(B_150) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_752])).
% 3.21/1.54  tff(c_771, plain, (![B_152, A_153]: (k2_relat_1(k5_relat_1(B_152, k6_relat_1(A_153)))=A_153 | ~r1_tarski(A_153, k2_relat_1(B_152)) | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_758])).
% 3.21/1.54  tff(c_790, plain, (![A_153, A_23]: (k2_relat_1(k7_relat_1(k6_relat_1(A_153), A_23))=A_153 | ~r1_tarski(A_153, k2_relat_1(k6_relat_1(A_23))) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_153)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_771])).
% 3.21/1.54  tff(c_797, plain, (![A_153, A_23]: (k3_xboole_0(A_153, A_23)=A_153 | ~r1_tarski(A_153, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_24, c_24, c_710, c_790])).
% 3.21/1.54  tff(c_967, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_959, c_797])).
% 3.21/1.54  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.54  tff(c_559, plain, (![A_112, B_113]: (k1_setfam_1(k2_tarski(A_112, B_113))=k3_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.54  tff(c_574, plain, (![B_114, A_115]: (k1_setfam_1(k2_tarski(B_114, A_115))=k3_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_2, c_559])).
% 3.21/1.54  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.54  tff(c_580, plain, (![B_114, A_115]: (k3_xboole_0(B_114, A_115)=k3_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_574, c_8])).
% 3.21/1.54  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.54  tff(c_804, plain, (![A_158, A_159]: (k3_xboole_0(A_158, A_159)=A_158 | ~r1_tarski(A_158, A_159))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_24, c_24, c_710, c_790])).
% 3.21/1.54  tff(c_854, plain, (![B_166, A_167]: (k3_xboole_0(k2_relat_1(B_166), A_167)=k2_relat_1(B_166) | ~v5_relat_1(B_166, A_167) | ~v1_relat_1(B_166))), inference(resolution, [status(thm)], [c_14, c_804])).
% 3.21/1.54  tff(c_880, plain, (![A_115, B_166]: (k3_xboole_0(A_115, k2_relat_1(B_166))=k2_relat_1(B_166) | ~v5_relat_1(B_166, A_115) | ~v1_relat_1(B_166))), inference(superposition, [status(thm), theory('equality')], [c_580, c_854])).
% 3.21/1.54  tff(c_971, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_967, c_880])).
% 3.21/1.54  tff(c_978, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_636, c_678, c_971])).
% 3.21/1.54  tff(c_980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_766, c_978])).
% 3.21/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.54  
% 3.21/1.54  Inference rules
% 3.21/1.54  ----------------------
% 3.21/1.54  #Ref     : 0
% 3.21/1.54  #Sup     : 225
% 3.21/1.54  #Fact    : 0
% 3.21/1.54  #Define  : 0
% 3.21/1.54  #Split   : 1
% 3.21/1.54  #Chain   : 0
% 3.21/1.54  #Close   : 0
% 3.21/1.54  
% 3.21/1.54  Ordering : KBO
% 3.21/1.54  
% 3.21/1.54  Simplification rules
% 3.21/1.54  ----------------------
% 3.21/1.54  #Subsume      : 15
% 3.21/1.54  #Demod        : 81
% 3.21/1.54  #Tautology    : 119
% 3.21/1.54  #SimpNegUnit  : 2
% 3.21/1.54  #BackRed      : 4
% 3.21/1.54  
% 3.21/1.54  #Partial instantiations: 0
% 3.21/1.54  #Strategies tried      : 1
% 3.21/1.54  
% 3.21/1.54  Timing (in seconds)
% 3.21/1.54  ----------------------
% 3.21/1.54  Preprocessing        : 0.34
% 3.21/1.54  Parsing              : 0.19
% 3.21/1.54  CNF conversion       : 0.02
% 3.21/1.54  Main loop            : 0.36
% 3.21/1.54  Inferencing          : 0.14
% 3.21/1.54  Reduction            : 0.12
% 3.21/1.54  Demodulation         : 0.09
% 3.21/1.54  BG Simplification    : 0.02
% 3.21/1.54  Subsumption          : 0.05
% 3.21/1.54  Abstraction          : 0.02
% 3.21/1.54  MUC search           : 0.00
% 3.21/1.54  Cooper               : 0.00
% 3.21/1.54  Total                : 0.74
% 3.21/1.54  Index Insertion      : 0.00
% 3.21/1.54  Index Deletion       : 0.00
% 3.21/1.54  Index Matching       : 0.00
% 3.21/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
