%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:07 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 111 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 168 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_399,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_408,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_399])).

tff(c_573,plain,(
    ! [A_139,B_140,C_141] :
      ( m1_subset_1(k2_relset_1(A_139,B_140,C_141),k1_zfmisc_1(B_140))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_594,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_573])).

tff(c_601,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_594])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_609,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_601,c_12])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_64])).

tff(c_163,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_172,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_22])).

tff(c_178,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_175])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_182,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_24])).

tff(c_186,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_182])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [A_58,A_7,B_8] :
      ( r1_tarski(A_58,k2_xboole_0(A_7,B_8))
      | ~ r1_tarski(A_58,A_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_18,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_292,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_tarski(k2_xboole_0(A_95,C_96),B_97)
      | ~ r1_tarski(C_96,B_97)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1402,plain,(
    ! [A_239,B_240] :
      ( r1_tarski(k3_relat_1(A_239),B_240)
      | ~ r1_tarski(k2_relat_1(A_239),B_240)
      | ~ r1_tarski(k1_relat_1(A_239),B_240)
      | ~ v1_relat_1(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_292])).

tff(c_34,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1481,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1402,c_34])).

tff(c_1510,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1481])).

tff(c_1545,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1510])).

tff(c_1554,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_108,c_1545])).

tff(c_1563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1554])).

tff(c_1564,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1510])).

tff(c_1577,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1564])).

tff(c_1584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_1577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.67  
% 3.80/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.67  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.80/1.67  
% 3.80/1.67  %Foreground sorts:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Background operators:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Foreground operators:
% 3.80/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.80/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.80/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.80/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.80/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.80/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.67  
% 3.80/1.68  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.80/1.68  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.80/1.68  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.80/1.68  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.80/1.68  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.80/1.68  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.80/1.68  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.80/1.68  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.80/1.68  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.80/1.68  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.80/1.68  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.80/1.68  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.80/1.68  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.80/1.68  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.80/1.68  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.80/1.68  tff(c_399, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.80/1.68  tff(c_408, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_399])).
% 3.80/1.68  tff(c_573, plain, (![A_139, B_140, C_141]: (m1_subset_1(k2_relset_1(A_139, B_140, C_141), k1_zfmisc_1(B_140)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.80/1.68  tff(c_594, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_408, c_573])).
% 3.80/1.68  tff(c_601, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_594])).
% 3.80/1.68  tff(c_12, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.80/1.68  tff(c_609, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_601, c_12])).
% 3.80/1.68  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.80/1.68  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/1.68  tff(c_58, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.68  tff(c_64, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_58])).
% 3.80/1.68  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_64])).
% 3.80/1.68  tff(c_163, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.80/1.68  tff(c_172, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_163])).
% 3.80/1.68  tff(c_22, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.68  tff(c_175, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_172, c_22])).
% 3.80/1.68  tff(c_178, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_175])).
% 3.80/1.68  tff(c_24, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.80/1.68  tff(c_182, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_24])).
% 3.80/1.68  tff(c_186, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_182])).
% 3.80/1.68  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.80/1.68  tff(c_96, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.80/1.68  tff(c_108, plain, (![A_58, A_7, B_8]: (r1_tarski(A_58, k2_xboole_0(A_7, B_8)) | ~r1_tarski(A_58, A_7))), inference(resolution, [status(thm)], [c_6, c_96])).
% 3.80/1.68  tff(c_18, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.80/1.68  tff(c_292, plain, (![A_95, C_96, B_97]: (r1_tarski(k2_xboole_0(A_95, C_96), B_97) | ~r1_tarski(C_96, B_97) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.80/1.68  tff(c_1402, plain, (![A_239, B_240]: (r1_tarski(k3_relat_1(A_239), B_240) | ~r1_tarski(k2_relat_1(A_239), B_240) | ~r1_tarski(k1_relat_1(A_239), B_240) | ~v1_relat_1(A_239))), inference(superposition, [status(thm), theory('equality')], [c_18, c_292])).
% 3.80/1.68  tff(c_34, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.80/1.68  tff(c_1481, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1402, c_34])).
% 3.80/1.68  tff(c_1510, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1481])).
% 3.80/1.68  tff(c_1545, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1510])).
% 3.80/1.68  tff(c_1554, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_108, c_1545])).
% 3.80/1.68  tff(c_1563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_1554])).
% 3.80/1.68  tff(c_1564, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1510])).
% 3.80/1.68  tff(c_1577, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_1564])).
% 3.80/1.68  tff(c_1584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_609, c_1577])).
% 3.80/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.68  
% 3.80/1.68  Inference rules
% 3.80/1.68  ----------------------
% 3.80/1.68  #Ref     : 0
% 3.80/1.68  #Sup     : 360
% 3.80/1.68  #Fact    : 0
% 3.80/1.68  #Define  : 0
% 3.80/1.68  #Split   : 12
% 3.80/1.68  #Chain   : 0
% 3.80/1.68  #Close   : 0
% 3.80/1.68  
% 3.80/1.68  Ordering : KBO
% 3.80/1.68  
% 3.80/1.68  Simplification rules
% 3.80/1.68  ----------------------
% 3.80/1.68  #Subsume      : 231
% 3.80/1.68  #Demod        : 39
% 3.80/1.68  #Tautology    : 30
% 3.80/1.68  #SimpNegUnit  : 45
% 3.80/1.68  #BackRed      : 8
% 3.80/1.68  
% 3.80/1.68  #Partial instantiations: 0
% 3.80/1.68  #Strategies tried      : 1
% 3.80/1.68  
% 3.80/1.68  Timing (in seconds)
% 3.80/1.68  ----------------------
% 3.80/1.69  Preprocessing        : 0.31
% 3.80/1.69  Parsing              : 0.17
% 3.80/1.69  CNF conversion       : 0.02
% 3.80/1.69  Main loop            : 0.60
% 3.80/1.69  Inferencing          : 0.21
% 3.80/1.69  Reduction            : 0.17
% 3.80/1.69  Demodulation         : 0.11
% 3.80/1.69  BG Simplification    : 0.02
% 3.80/1.69  Subsumption          : 0.15
% 3.80/1.69  Abstraction          : 0.03
% 3.80/1.69  MUC search           : 0.00
% 3.80/1.69  Cooper               : 0.00
% 3.80/1.69  Total                : 0.94
% 3.80/1.69  Index Insertion      : 0.00
% 3.80/1.69  Index Deletion       : 0.00
% 3.80/1.69  Index Matching       : 0.00
% 3.80/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
