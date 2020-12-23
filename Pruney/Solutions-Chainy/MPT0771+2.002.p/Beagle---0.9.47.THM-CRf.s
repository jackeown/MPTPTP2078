%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:37 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 142 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 260 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k3_relat_1(k2_wellord1(B,A)),k3_relat_1(B))
          & r1_tarski(k3_relat_1(k2_wellord1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k8_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( k8_relat_1(A_29,k7_relat_1(B_30,A_29)) = k2_wellord1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_255,plain,(
    ! [A_94,C_95,B_96] :
      ( k8_relat_1(A_94,k7_relat_1(C_95,B_96)) = k7_relat_1(k8_relat_1(A_94,C_95),B_96)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_292,plain,(
    ! [A_102,B_103] :
      ( k7_relat_1(k8_relat_1(A_102,B_103),A_102) = k2_wellord1(B_103,A_102)
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_255])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_420,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(k1_relat_1(k2_wellord1(B_122,A_123)),A_123)
      | ~ v1_relat_1(k8_relat_1(A_123,B_122))
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_24])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_218,plain,(
    ! [A_83,B_84] :
      ( k8_relat_1(A_83,k7_relat_1(B_84,A_83)) = k2_wellord1(B_84,A_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_16,B_17)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_227,plain,(
    ! [B_84,A_83] :
      ( r1_tarski(k2_relat_1(k2_wellord1(B_84,A_83)),A_83)
      | ~ v1_relat_1(k7_relat_1(B_84,A_83))
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_18])).

tff(c_203,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,k2_zfmisc_1(B_82,B_82)) = k2_wellord1(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_236,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k2_wellord1(A_85,B_86),A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(A_6)
      | ~ v1_relat_1(B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_42])).

tff(c_240,plain,(
    ! [A_85,B_86] :
      ( v1_relat_1(k2_wellord1(A_85,B_86))
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_236,c_46])).

tff(c_12,plain,(
    ! [A_11] :
      ( k2_xboole_0(k1_relat_1(A_11),k2_relat_1(A_11)) = k3_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_242,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_tarski(k2_xboole_0(A_89,C_90),B_91)
      | ~ r1_tarski(C_90,B_91)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_356,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(k3_relat_1(A_115),B_116)
      | ~ r1_tarski(k2_relat_1(A_115),B_116)
      | ~ r1_tarski(k1_relat_1(A_115),B_116)
      | ~ v1_relat_1(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_242])).

tff(c_93,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,k2_zfmisc_1(B_59,B_59)) = k2_wellord1(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_102,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k2_wellord1(A_58,B_59),A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_108,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k2_wellord1(A_60,B_61),A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_112,plain,(
    ! [A_60,B_61] :
      ( v1_relat_1(k2_wellord1(A_60,B_61))
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_108,c_46])).

tff(c_147,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k3_relat_1(A_70),k3_relat_1(B_71))
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_150,plain,
    ( ~ r1_tarski(k2_wellord1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_147,c_53])).

tff(c_156,plain,
    ( ~ r1_tarski(k2_wellord1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_150])).

tff(c_158,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_161,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_161])).

tff(c_166,plain,(
    ~ r1_tarski(k2_wellord1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_170,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_166])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_170])).

tff(c_175,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_366,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_356,c_175])).

tff(c_386,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_389,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_240,c_386])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_389])).

tff(c_394,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_396,plain,(
    ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_399,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_227,c_396])).

tff(c_402,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_399])).

tff(c_405,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_402])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_405])).

tff(c_410,plain,(
    ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_423,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_420,c_410])).

tff(c_431,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_423])).

tff(c_436,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_431])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.38  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.71/1.38  
% 2.71/1.38  %Foreground sorts:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Background operators:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Foreground operators:
% 2.71/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.71/1.38  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.71/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.71/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.38  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.71/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.38  
% 2.71/1.40  tff(f_93, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k3_relat_1(k2_wellord1(B, A)), k3_relat_1(B)) & r1_tarski(k3_relat_1(k2_wellord1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_wellord1)).
% 2.71/1.40  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.71/1.40  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 2.71/1.40  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 2.71/1.40  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.71/1.40  tff(f_52, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.71/1.40  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.71/1.40  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 2.71/1.40  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.71/1.40  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.40  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.40  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.71/1.40  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.71/1.40  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.71/1.40  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.40  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k8_relat_1(A_14, B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.71/1.40  tff(c_28, plain, (![A_29, B_30]: (k8_relat_1(A_29, k7_relat_1(B_30, A_29))=k2_wellord1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.71/1.40  tff(c_255, plain, (![A_94, C_95, B_96]: (k8_relat_1(A_94, k7_relat_1(C_95, B_96))=k7_relat_1(k8_relat_1(A_94, C_95), B_96) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.40  tff(c_292, plain, (![A_102, B_103]: (k7_relat_1(k8_relat_1(A_102, B_103), A_102)=k2_wellord1(B_103, A_102) | ~v1_relat_1(B_103) | ~v1_relat_1(B_103))), inference(superposition, [status(thm), theory('equality')], [c_28, c_255])).
% 2.71/1.40  tff(c_24, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.71/1.40  tff(c_420, plain, (![B_122, A_123]: (r1_tarski(k1_relat_1(k2_wellord1(B_122, A_123)), A_123) | ~v1_relat_1(k8_relat_1(A_123, B_122)) | ~v1_relat_1(B_122) | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_292, c_24])).
% 2.71/1.40  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.40  tff(c_218, plain, (![A_83, B_84]: (k8_relat_1(A_83, k7_relat_1(B_84, A_83))=k2_wellord1(B_84, A_83) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.71/1.40  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k2_relat_1(k8_relat_1(A_16, B_17)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.40  tff(c_227, plain, (![B_84, A_83]: (r1_tarski(k2_relat_1(k2_wellord1(B_84, A_83)), A_83) | ~v1_relat_1(k7_relat_1(B_84, A_83)) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_218, c_18])).
% 2.71/1.40  tff(c_203, plain, (![A_81, B_82]: (k3_xboole_0(A_81, k2_zfmisc_1(B_82, B_82))=k2_wellord1(A_81, B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.40  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.40  tff(c_236, plain, (![A_85, B_86]: (r1_tarski(k2_wellord1(A_85, B_86), A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 2.71/1.40  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.40  tff(c_42, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.40  tff(c_46, plain, (![A_6, B_7]: (v1_relat_1(A_6) | ~v1_relat_1(B_7) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_42])).
% 2.71/1.40  tff(c_240, plain, (![A_85, B_86]: (v1_relat_1(k2_wellord1(A_85, B_86)) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_236, c_46])).
% 2.71/1.40  tff(c_12, plain, (![A_11]: (k2_xboole_0(k1_relat_1(A_11), k2_relat_1(A_11))=k3_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.71/1.40  tff(c_242, plain, (![A_89, C_90, B_91]: (r1_tarski(k2_xboole_0(A_89, C_90), B_91) | ~r1_tarski(C_90, B_91) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.40  tff(c_356, plain, (![A_115, B_116]: (r1_tarski(k3_relat_1(A_115), B_116) | ~r1_tarski(k2_relat_1(A_115), B_116) | ~r1_tarski(k1_relat_1(A_115), B_116) | ~v1_relat_1(A_115))), inference(superposition, [status(thm), theory('equality')], [c_12, c_242])).
% 2.71/1.40  tff(c_93, plain, (![A_58, B_59]: (k3_xboole_0(A_58, k2_zfmisc_1(B_59, B_59))=k2_wellord1(A_58, B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.40  tff(c_102, plain, (![A_58, B_59]: (r1_tarski(k2_wellord1(A_58, B_59), A_58) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2])).
% 2.71/1.40  tff(c_108, plain, (![A_60, B_61]: (r1_tarski(k2_wellord1(A_60, B_61), A_60) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2])).
% 2.71/1.40  tff(c_112, plain, (![A_60, B_61]: (v1_relat_1(k2_wellord1(A_60, B_61)) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_108, c_46])).
% 2.71/1.40  tff(c_147, plain, (![A_70, B_71]: (r1_tarski(k3_relat_1(A_70), k3_relat_1(B_71)) | ~r1_tarski(A_70, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.40  tff(c_30, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.40  tff(c_53, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.71/1.40  tff(c_150, plain, (~r1_tarski(k2_wellord1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_147, c_53])).
% 2.71/1.40  tff(c_156, plain, (~r1_tarski(k2_wellord1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_150])).
% 2.71/1.40  tff(c_158, plain, (~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_156])).
% 2.71/1.40  tff(c_161, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_112, c_158])).
% 2.71/1.40  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_161])).
% 2.71/1.40  tff(c_166, plain, (~r1_tarski(k2_wellord1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_156])).
% 2.71/1.40  tff(c_170, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_102, c_166])).
% 2.71/1.40  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_170])).
% 2.71/1.40  tff(c_175, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.71/1.40  tff(c_366, plain, (~r1_tarski(k2_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~r1_tarski(k1_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_356, c_175])).
% 2.71/1.40  tff(c_386, plain, (~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_366])).
% 2.71/1.40  tff(c_389, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_240, c_386])).
% 2.71/1.40  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_389])).
% 2.71/1.40  tff(c_394, plain, (~r1_tarski(k1_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~r1_tarski(k2_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_366])).
% 2.71/1.40  tff(c_396, plain, (~r1_tarski(k2_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitLeft, [status(thm)], [c_394])).
% 2.71/1.40  tff(c_399, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_227, c_396])).
% 2.71/1.40  tff(c_402, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_399])).
% 2.71/1.40  tff(c_405, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_402])).
% 2.71/1.40  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_405])).
% 2.71/1.40  tff(c_410, plain, (~r1_tarski(k1_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_394])).
% 2.71/1.40  tff(c_423, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_420, c_410])).
% 2.71/1.40  tff(c_431, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_423])).
% 2.71/1.40  tff(c_436, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_431])).
% 2.71/1.40  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_436])).
% 2.71/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  Inference rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Ref     : 0
% 2.71/1.40  #Sup     : 94
% 2.71/1.40  #Fact    : 0
% 2.71/1.40  #Define  : 0
% 2.71/1.40  #Split   : 6
% 2.71/1.40  #Chain   : 0
% 2.71/1.40  #Close   : 0
% 2.71/1.40  
% 2.71/1.40  Ordering : KBO
% 2.71/1.40  
% 2.71/1.40  Simplification rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Subsume      : 12
% 2.71/1.40  #Demod        : 8
% 2.71/1.40  #Tautology    : 19
% 2.71/1.40  #SimpNegUnit  : 0
% 2.71/1.40  #BackRed      : 0
% 2.71/1.40  
% 2.71/1.40  #Partial instantiations: 0
% 2.71/1.40  #Strategies tried      : 1
% 2.71/1.40  
% 2.71/1.40  Timing (in seconds)
% 2.71/1.40  ----------------------
% 2.71/1.40  Preprocessing        : 0.32
% 2.71/1.40  Parsing              : 0.17
% 2.71/1.40  CNF conversion       : 0.02
% 2.71/1.40  Main loop            : 0.30
% 2.71/1.40  Inferencing          : 0.13
% 2.71/1.40  Reduction            : 0.07
% 2.71/1.40  Demodulation         : 0.05
% 2.71/1.40  BG Simplification    : 0.02
% 2.71/1.40  Subsumption          : 0.06
% 2.71/1.40  Abstraction          : 0.02
% 2.71/1.40  MUC search           : 0.00
% 2.71/1.40  Cooper               : 0.00
% 2.71/1.40  Total                : 0.65
% 2.71/1.40  Index Insertion      : 0.00
% 2.71/1.40  Index Deletion       : 0.00
% 2.71/1.40  Index Matching       : 0.00
% 2.71/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
