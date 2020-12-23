%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:07 EST 2020

% Result     : Theorem 6.58s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   72 (  95 expanded)
%              Number of leaves         :   37 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 130 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_834,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relset_1(A_122,B_123,C_124) = k2_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_843,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_834])).

tff(c_976,plain,(
    ! [A_140,B_141,C_142] :
      ( m1_subset_1(k2_relset_1(A_140,B_141,C_142),k1_zfmisc_1(B_141))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_997,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_976])).

tff(c_1004,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_997])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1012,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1004,c_16])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_115,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_121])).

tff(c_259,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_268,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_259])).

tff(c_26,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = B_27
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_272,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_268,c_26])).

tff(c_275,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_272])).

tff(c_28,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_29,A_28)),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_279,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_28])).

tff(c_283,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_279])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_292,plain,(
    k2_xboole_0(k1_relat_1('#skF_3'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_283,c_6])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(k2_xboole_0(A_55,B_57),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [A_55,B_57,B_10] : r1_tarski(A_55,k2_xboole_0(k2_xboole_0(A_55,B_57),B_10)) ),
    inference(resolution,[status(thm)],[c_8,c_85])).

tff(c_329,plain,(
    ! [B_10] : r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1',B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_90])).

tff(c_22,plain,(
    ! [A_23] :
      ( k2_xboole_0(k1_relat_1(A_23),k2_relat_1(A_23)) = k3_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_613,plain,(
    ! [A_108,C_109,B_110] :
      ( r1_tarski(k2_xboole_0(A_108,C_109),B_110)
      | ~ r1_tarski(C_109,B_110)
      | ~ r1_tarski(A_108,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3556,plain,(
    ! [A_261,B_262] :
      ( r1_tarski(k3_relat_1(A_261),B_262)
      | ~ r1_tarski(k2_relat_1(A_261),B_262)
      | ~ r1_tarski(k1_relat_1(A_261),B_262)
      | ~ v1_relat_1(A_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_613])).

tff(c_38,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3587,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3556,c_38])).

tff(c_3600,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_329,c_3587])).

tff(c_3616,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_3600])).

tff(c_3623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_3616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.58/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.73  
% 6.58/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.73  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.58/2.73  
% 6.58/2.73  %Foreground sorts:
% 6.58/2.73  
% 6.58/2.73  
% 6.58/2.73  %Background operators:
% 6.58/2.73  
% 6.58/2.73  
% 6.58/2.73  %Foreground operators:
% 6.58/2.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.58/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.58/2.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.58/2.73  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.58/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.58/2.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.58/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.58/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.58/2.73  tff('#skF_2', type, '#skF_2': $i).
% 6.58/2.73  tff('#skF_3', type, '#skF_3': $i).
% 6.58/2.73  tff('#skF_1', type, '#skF_1': $i).
% 6.58/2.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.58/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.58/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.58/2.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.58/2.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.58/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.58/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.58/2.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.58/2.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.58/2.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.58/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.58/2.73  
% 6.58/2.75  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 6.58/2.75  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.58/2.75  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.58/2.75  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.58/2.75  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.58/2.75  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.58/2.75  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.58/2.75  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.58/2.75  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.58/2.75  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 6.58/2.75  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.58/2.75  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.58/2.75  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.58/2.75  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 6.58/2.75  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.58/2.75  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.58/2.75  tff(c_834, plain, (![A_122, B_123, C_124]: (k2_relset_1(A_122, B_123, C_124)=k2_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.58/2.75  tff(c_843, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_834])).
% 6.58/2.75  tff(c_976, plain, (![A_140, B_141, C_142]: (m1_subset_1(k2_relset_1(A_140, B_141, C_142), k1_zfmisc_1(B_141)) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.58/2.75  tff(c_997, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_843, c_976])).
% 6.58/2.75  tff(c_1004, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_997])).
% 6.58/2.75  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.58/2.75  tff(c_1012, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1004, c_16])).
% 6.58/2.75  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.58/2.75  tff(c_24, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.58/2.75  tff(c_115, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.58/2.75  tff(c_121, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_115])).
% 6.58/2.75  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_121])).
% 6.58/2.75  tff(c_259, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.58/2.75  tff(c_268, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_259])).
% 6.58/2.75  tff(c_26, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=B_27 | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.58/2.75  tff(c_272, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_268, c_26])).
% 6.58/2.75  tff(c_275, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_272])).
% 6.58/2.75  tff(c_28, plain, (![B_29, A_28]: (r1_tarski(k1_relat_1(k7_relat_1(B_29, A_28)), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.58/2.75  tff(c_279, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_275, c_28])).
% 6.58/2.75  tff(c_283, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_279])).
% 6.58/2.75  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.58/2.75  tff(c_292, plain, (k2_xboole_0(k1_relat_1('#skF_3'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_283, c_6])).
% 6.58/2.75  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.58/2.75  tff(c_85, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(k2_xboole_0(A_55, B_57), C_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.58/2.75  tff(c_90, plain, (![A_55, B_57, B_10]: (r1_tarski(A_55, k2_xboole_0(k2_xboole_0(A_55, B_57), B_10)))), inference(resolution, [status(thm)], [c_8, c_85])).
% 6.58/2.75  tff(c_329, plain, (![B_10]: (r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', B_10)))), inference(superposition, [status(thm), theory('equality')], [c_292, c_90])).
% 6.58/2.75  tff(c_22, plain, (![A_23]: (k2_xboole_0(k1_relat_1(A_23), k2_relat_1(A_23))=k3_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.58/2.75  tff(c_613, plain, (![A_108, C_109, B_110]: (r1_tarski(k2_xboole_0(A_108, C_109), B_110) | ~r1_tarski(C_109, B_110) | ~r1_tarski(A_108, B_110))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.58/2.75  tff(c_3556, plain, (![A_261, B_262]: (r1_tarski(k3_relat_1(A_261), B_262) | ~r1_tarski(k2_relat_1(A_261), B_262) | ~r1_tarski(k1_relat_1(A_261), B_262) | ~v1_relat_1(A_261))), inference(superposition, [status(thm), theory('equality')], [c_22, c_613])).
% 6.58/2.75  tff(c_38, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.58/2.75  tff(c_3587, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3556, c_38])).
% 6.58/2.75  tff(c_3600, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_329, c_3587])).
% 6.58/2.75  tff(c_3616, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_3600])).
% 6.58/2.75  tff(c_3623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1012, c_3616])).
% 6.58/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.75  
% 6.58/2.75  Inference rules
% 6.58/2.75  ----------------------
% 6.58/2.75  #Ref     : 0
% 6.58/2.75  #Sup     : 903
% 6.58/2.75  #Fact    : 0
% 6.58/2.75  #Define  : 0
% 6.58/2.75  #Split   : 17
% 6.58/2.75  #Chain   : 0
% 6.58/2.75  #Close   : 0
% 6.58/2.75  
% 6.58/2.75  Ordering : KBO
% 6.58/2.75  
% 6.58/2.75  Simplification rules
% 6.58/2.75  ----------------------
% 6.58/2.75  #Subsume      : 485
% 6.58/2.75  #Demod        : 176
% 6.58/2.75  #Tautology    : 214
% 6.58/2.75  #SimpNegUnit  : 46
% 6.58/2.75  #BackRed      : 12
% 6.58/2.75  
% 6.58/2.75  #Partial instantiations: 0
% 6.58/2.75  #Strategies tried      : 1
% 6.58/2.75  
% 6.58/2.75  Timing (in seconds)
% 6.58/2.75  ----------------------
% 6.58/2.76  Preprocessing        : 0.52
% 6.58/2.76  Parsing              : 0.27
% 6.58/2.76  CNF conversion       : 0.03
% 6.58/2.76  Main loop            : 1.35
% 6.58/2.76  Inferencing          : 0.46
% 6.58/2.76  Reduction            : 0.46
% 6.58/2.76  Demodulation         : 0.34
% 6.58/2.76  BG Simplification    : 0.05
% 6.58/2.76  Subsumption          : 0.28
% 6.58/2.76  Abstraction          : 0.06
% 6.58/2.76  MUC search           : 0.00
% 6.58/2.76  Cooper               : 0.00
% 6.58/2.76  Total                : 1.92
% 6.58/2.76  Index Insertion      : 0.00
% 6.58/2.76  Index Deletion       : 0.00
% 6.58/2.76  Index Matching       : 0.00
% 6.58/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
