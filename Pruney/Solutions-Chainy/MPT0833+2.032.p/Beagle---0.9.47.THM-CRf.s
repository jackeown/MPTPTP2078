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
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   62 (  86 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   92 ( 139 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_426,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( r2_relset_1(A_101,B_102,C_103,C_103)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_434,plain,(
    ! [C_105] :
      ( r2_relset_1('#skF_1','#skF_2',C_105,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_426])).

tff(c_441,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_434])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_79,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_34])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_15,B_16)),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_174,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k2_relat_1(A_64),k2_relat_1(B_65))
      | ~ r1_tarski(A_64,B_65)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_879,plain,(
    ! [A_166,B_167] :
      ( k2_xboole_0(k2_relat_1(A_166),k2_relat_1(B_167)) = k2_relat_1(B_167)
      | ~ r1_tarski(A_166,B_167)
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(A_166) ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1754,plain,(
    ! [A_237,C_238,B_239] :
      ( r1_tarski(k2_relat_1(A_237),C_238)
      | ~ r1_tarski(k2_relat_1(B_239),C_238)
      | ~ r1_tarski(A_237,B_239)
      | ~ v1_relat_1(B_239)
      | ~ v1_relat_1(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_2])).

tff(c_1776,plain,(
    ! [A_237,B_16,A_15] :
      ( r1_tarski(k2_relat_1(A_237),B_16)
      | ~ r1_tarski(A_237,k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(A_237) ) ),
    inference(resolution,[status(thm)],[c_16,c_1754])).

tff(c_1817,plain,(
    ! [A_244,B_245,A_246] :
      ( r1_tarski(k2_relat_1(A_244),B_245)
      | ~ r1_tarski(A_244,k2_zfmisc_1(A_246,B_245))
      | ~ v1_relat_1(A_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1776])).

tff(c_1839,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1817])).

tff(c_1852,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1839])).

tff(c_1885,plain,(
    k2_xboole_0(k2_relat_1('#skF_4'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1852,c_4])).

tff(c_1934,plain,(
    ! [C_250] :
      ( r1_tarski(k2_relat_1('#skF_4'),C_250)
      | ~ r1_tarski('#skF_2',C_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_2])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k8_relat_1(A_13,B_14) = B_14
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1987,plain,(
    ! [C_250] :
      ( k8_relat_1(C_250,'#skF_4') = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',C_250) ) ),
    inference(resolution,[status(thm)],[c_1934,c_14])).

tff(c_2019,plain,(
    ! [C_251] :
      ( k8_relat_1(C_251,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',C_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1987])).

tff(c_2027,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_2019])).

tff(c_279,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k6_relset_1(A_79,B_80,C_81,D_82) = k8_relat_1(C_81,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_286,plain,(
    ! [C_81] : k6_relset_1('#skF_1','#skF_2',C_81,'#skF_4') = k8_relat_1(C_81,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_279])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_287,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_26])).

tff(c_2028,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2027,c_287])).

tff(c_2031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_2028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.65  
% 3.90/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.65  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.90/1.65  
% 3.90/1.65  %Foreground sorts:
% 3.90/1.65  
% 3.90/1.65  
% 3.90/1.65  %Background operators:
% 3.90/1.65  
% 3.90/1.65  
% 3.90/1.65  %Foreground operators:
% 3.90/1.65  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.90/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.65  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.90/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.90/1.65  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 3.90/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.90/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.90/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.65  
% 3.90/1.67  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 3.90/1.67  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.90/1.67  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.90/1.67  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.90/1.67  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.90/1.67  tff(f_54, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 3.90/1.67  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.90/1.67  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.90/1.67  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.90/1.67  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 3.90/1.67  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 3.90/1.67  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.90/1.67  tff(c_426, plain, (![A_101, B_102, C_103, D_104]: (r2_relset_1(A_101, B_102, C_103, C_103) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.67  tff(c_434, plain, (![C_105]: (r2_relset_1('#skF_1', '#skF_2', C_105, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_426])).
% 3.90/1.67  tff(c_441, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_434])).
% 3.90/1.67  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.90/1.67  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.90/1.67  tff(c_69, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.90/1.67  tff(c_75, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_69])).
% 3.90/1.67  tff(c_79, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_75])).
% 3.90/1.67  tff(c_34, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.90/1.67  tff(c_42, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_34])).
% 3.90/1.67  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_15, B_16)), B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.90/1.67  tff(c_174, plain, (![A_64, B_65]: (r1_tarski(k2_relat_1(A_64), k2_relat_1(B_65)) | ~r1_tarski(A_64, B_65) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.90/1.67  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.67  tff(c_879, plain, (![A_166, B_167]: (k2_xboole_0(k2_relat_1(A_166), k2_relat_1(B_167))=k2_relat_1(B_167) | ~r1_tarski(A_166, B_167) | ~v1_relat_1(B_167) | ~v1_relat_1(A_166))), inference(resolution, [status(thm)], [c_174, c_4])).
% 3.90/1.67  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.90/1.67  tff(c_1754, plain, (![A_237, C_238, B_239]: (r1_tarski(k2_relat_1(A_237), C_238) | ~r1_tarski(k2_relat_1(B_239), C_238) | ~r1_tarski(A_237, B_239) | ~v1_relat_1(B_239) | ~v1_relat_1(A_237))), inference(superposition, [status(thm), theory('equality')], [c_879, c_2])).
% 3.90/1.67  tff(c_1776, plain, (![A_237, B_16, A_15]: (r1_tarski(k2_relat_1(A_237), B_16) | ~r1_tarski(A_237, k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(A_237))), inference(resolution, [status(thm)], [c_16, c_1754])).
% 3.90/1.67  tff(c_1817, plain, (![A_244, B_245, A_246]: (r1_tarski(k2_relat_1(A_244), B_245) | ~r1_tarski(A_244, k2_zfmisc_1(A_246, B_245)) | ~v1_relat_1(A_244))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1776])).
% 3.90/1.67  tff(c_1839, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1817])).
% 3.90/1.67  tff(c_1852, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1839])).
% 3.90/1.67  tff(c_1885, plain, (k2_xboole_0(k2_relat_1('#skF_4'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_1852, c_4])).
% 3.90/1.67  tff(c_1934, plain, (![C_250]: (r1_tarski(k2_relat_1('#skF_4'), C_250) | ~r1_tarski('#skF_2', C_250))), inference(superposition, [status(thm), theory('equality')], [c_1885, c_2])).
% 3.90/1.67  tff(c_14, plain, (![A_13, B_14]: (k8_relat_1(A_13, B_14)=B_14 | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.90/1.67  tff(c_1987, plain, (![C_250]: (k8_relat_1(C_250, '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', C_250))), inference(resolution, [status(thm)], [c_1934, c_14])).
% 3.90/1.67  tff(c_2019, plain, (![C_251]: (k8_relat_1(C_251, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', C_251))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1987])).
% 3.90/1.67  tff(c_2027, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_2019])).
% 3.90/1.67  tff(c_279, plain, (![A_79, B_80, C_81, D_82]: (k6_relset_1(A_79, B_80, C_81, D_82)=k8_relat_1(C_81, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.90/1.67  tff(c_286, plain, (![C_81]: (k6_relset_1('#skF_1', '#skF_2', C_81, '#skF_4')=k8_relat_1(C_81, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_279])).
% 3.90/1.67  tff(c_26, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.90/1.67  tff(c_287, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_26])).
% 3.90/1.67  tff(c_2028, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2027, c_287])).
% 3.90/1.67  tff(c_2031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_441, c_2028])).
% 3.90/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.67  
% 3.90/1.67  Inference rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Ref     : 0
% 3.90/1.67  #Sup     : 450
% 3.90/1.67  #Fact    : 0
% 3.90/1.67  #Define  : 0
% 3.90/1.67  #Split   : 8
% 3.90/1.67  #Chain   : 0
% 3.90/1.67  #Close   : 0
% 3.90/1.67  
% 3.90/1.67  Ordering : KBO
% 3.90/1.67  
% 3.90/1.67  Simplification rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Subsume      : 60
% 3.90/1.67  #Demod        : 82
% 3.90/1.67  #Tautology    : 153
% 3.90/1.67  #SimpNegUnit  : 0
% 3.90/1.67  #BackRed      : 2
% 3.90/1.67  
% 3.90/1.67  #Partial instantiations: 0
% 3.90/1.67  #Strategies tried      : 1
% 3.90/1.67  
% 3.90/1.67  Timing (in seconds)
% 3.90/1.67  ----------------------
% 3.90/1.67  Preprocessing        : 0.30
% 3.90/1.67  Parsing              : 0.16
% 3.90/1.67  CNF conversion       : 0.02
% 3.90/1.67  Main loop            : 0.61
% 3.90/1.67  Inferencing          : 0.22
% 3.90/1.67  Reduction            : 0.18
% 3.90/1.67  Demodulation         : 0.13
% 3.90/1.67  BG Simplification    : 0.02
% 3.90/1.67  Subsumption          : 0.13
% 3.90/1.67  Abstraction          : 0.03
% 3.90/1.67  MUC search           : 0.00
% 3.90/1.67  Cooper               : 0.00
% 3.90/1.67  Total                : 0.94
% 3.90/1.67  Index Insertion      : 0.00
% 3.90/1.67  Index Deletion       : 0.00
% 3.90/1.67  Index Matching       : 0.00
% 3.90/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
