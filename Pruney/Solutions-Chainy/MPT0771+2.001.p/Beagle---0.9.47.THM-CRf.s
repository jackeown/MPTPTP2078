%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:37 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 121 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 214 expanded)
%              Number of equality atoms :    8 (  12 expanded)
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

tff(f_97,negated_conjecture,(
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
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

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

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k8_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_207,plain,(
    ! [A_79,B_80] :
      ( k7_relat_1(k8_relat_1(A_79,B_80),A_79) = k2_wellord1(B_80,A_79)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_21)),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_213,plain,(
    ! [B_80,A_79] :
      ( r1_tarski(k1_relat_1(k2_wellord1(B_80,A_79)),A_79)
      | ~ v1_relat_1(k8_relat_1(A_79,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_22])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_227,plain,(
    ! [A_85,B_86] :
      ( k8_relat_1(A_85,k7_relat_1(B_86,A_85)) = k2_wellord1(B_86,A_85)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_16,B_17)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_239,plain,(
    ! [B_86,A_85] :
      ( r1_tarski(k2_relat_1(k2_wellord1(B_86,A_85)),A_85)
      | ~ v1_relat_1(k7_relat_1(B_86,A_85))
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_18])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( v1_relat_1(k2_wellord1(A_26,B_27))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_11] :
      ( k2_xboole_0(k1_relat_1(A_11),k2_relat_1(A_11)) = k3_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_271,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(k2_xboole_0(A_91,C_92),B_93)
      | ~ r1_tarski(C_92,B_93)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_294,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k3_relat_1(A_100),B_101)
      | ~ r1_tarski(k2_relat_1(A_100),B_101)
      | ~ r1_tarski(k1_relat_1(A_100),B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_271])).

tff(c_76,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,k2_zfmisc_1(B_56,B_56)) = k2_wellord1(A_55,B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k2_wellord1(A_55,B_56),A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2])).

tff(c_148,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k3_relat_1(A_70),k3_relat_1(B_71))
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_51,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_154,plain,
    ( ~ r1_tarski(k2_wellord1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_148,c_51])).

tff(c_158,plain,
    ( ~ r1_tarski(k2_wellord1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_154])).

tff(c_159,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_162,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_162])).

tff(c_167,plain,(
    ~ r1_tarski(k2_wellord1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_171,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_167])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_171])).

tff(c_176,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_302,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_294,c_176])).

tff(c_339,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_342,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_339])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_342])).

tff(c_347,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1')
    | ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_349,plain,(
    ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_352,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_239,c_349])).

tff(c_355,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_352])).

tff(c_358,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_355])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_358])).

tff(c_363,plain,(
    ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_373,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_213,c_363])).

tff(c_376,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_373])).

tff(c_379,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_376])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.43/1.35  
% 2.43/1.35  %Foreground sorts:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Background operators:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Foreground operators:
% 2.43/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.43/1.35  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.43/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.35  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.43/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.35  
% 2.58/1.37  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k3_relat_1(k2_wellord1(B, A)), k3_relat_1(B)) & r1_tarski(k3_relat_1(k2_wellord1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_wellord1)).
% 2.58/1.37  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.58/1.37  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 2.58/1.37  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.58/1.37  tff(f_52, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.58/1.37  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 2.58/1.37  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.58/1.37  tff(f_82, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 2.58/1.37  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.58/1.37  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.58/1.37  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 2.58/1.37  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.58/1.37  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.58/1.37  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.58/1.37  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k8_relat_1(A_14, B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.58/1.37  tff(c_207, plain, (![A_79, B_80]: (k7_relat_1(k8_relat_1(A_79, B_80), A_79)=k2_wellord1(B_80, A_79) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.37  tff(c_22, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_21)), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.58/1.37  tff(c_213, plain, (![B_80, A_79]: (r1_tarski(k1_relat_1(k2_wellord1(B_80, A_79)), A_79) | ~v1_relat_1(k8_relat_1(A_79, B_80)) | ~v1_relat_1(B_80))), inference(superposition, [status(thm), theory('equality')], [c_207, c_22])).
% 2.58/1.37  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.37  tff(c_227, plain, (![A_85, B_86]: (k8_relat_1(A_85, k7_relat_1(B_86, A_85))=k2_wellord1(B_86, A_85) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.58/1.37  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k2_relat_1(k8_relat_1(A_16, B_17)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.37  tff(c_239, plain, (![B_86, A_85]: (r1_tarski(k2_relat_1(k2_wellord1(B_86, A_85)), A_85) | ~v1_relat_1(k7_relat_1(B_86, A_85)) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_227, c_18])).
% 2.58/1.37  tff(c_26, plain, (![A_26, B_27]: (v1_relat_1(k2_wellord1(A_26, B_27)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.37  tff(c_12, plain, (![A_11]: (k2_xboole_0(k1_relat_1(A_11), k2_relat_1(A_11))=k3_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.58/1.37  tff(c_271, plain, (![A_91, C_92, B_93]: (r1_tarski(k2_xboole_0(A_91, C_92), B_93) | ~r1_tarski(C_92, B_93) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.37  tff(c_294, plain, (![A_100, B_101]: (r1_tarski(k3_relat_1(A_100), B_101) | ~r1_tarski(k2_relat_1(A_100), B_101) | ~r1_tarski(k1_relat_1(A_100), B_101) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_12, c_271])).
% 2.58/1.37  tff(c_76, plain, (![A_55, B_56]: (k3_xboole_0(A_55, k2_zfmisc_1(B_56, B_56))=k2_wellord1(A_55, B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.37  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.37  tff(c_85, plain, (![A_55, B_56]: (r1_tarski(k2_wellord1(A_55, B_56), A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_76, c_2])).
% 2.58/1.37  tff(c_148, plain, (![A_70, B_71]: (r1_tarski(k3_relat_1(A_70), k3_relat_1(B_71)) | ~r1_tarski(A_70, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.58/1.37  tff(c_32, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.58/1.37  tff(c_51, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.58/1.37  tff(c_154, plain, (~r1_tarski(k2_wellord1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_148, c_51])).
% 2.58/1.37  tff(c_158, plain, (~r1_tarski(k2_wellord1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_154])).
% 2.58/1.37  tff(c_159, plain, (~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_158])).
% 2.58/1.37  tff(c_162, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_159])).
% 2.58/1.37  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_162])).
% 2.58/1.37  tff(c_167, plain, (~r1_tarski(k2_wellord1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_158])).
% 2.58/1.37  tff(c_171, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_85, c_167])).
% 2.58/1.37  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_171])).
% 2.58/1.37  tff(c_176, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.58/1.37  tff(c_302, plain, (~r1_tarski(k2_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~r1_tarski(k1_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_294, c_176])).
% 2.58/1.37  tff(c_339, plain, (~v1_relat_1(k2_wellord1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_302])).
% 2.58/1.37  tff(c_342, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_339])).
% 2.58/1.37  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_342])).
% 2.58/1.37  tff(c_347, plain, (~r1_tarski(k1_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1') | ~r1_tarski(k2_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_302])).
% 2.58/1.37  tff(c_349, plain, (~r1_tarski(k2_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitLeft, [status(thm)], [c_347])).
% 2.58/1.37  tff(c_352, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_239, c_349])).
% 2.58/1.37  tff(c_355, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_352])).
% 2.58/1.37  tff(c_358, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_355])).
% 2.58/1.37  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_358])).
% 2.58/1.37  tff(c_363, plain, (~r1_tarski(k1_relat_1(k2_wellord1('#skF_2', '#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_347])).
% 2.58/1.37  tff(c_373, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_213, c_363])).
% 2.58/1.37  tff(c_376, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_373])).
% 2.58/1.37  tff(c_379, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_376])).
% 2.58/1.37  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_379])).
% 2.58/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  Inference rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Ref     : 0
% 2.58/1.37  #Sup     : 78
% 2.58/1.37  #Fact    : 0
% 2.58/1.37  #Define  : 0
% 2.58/1.37  #Split   : 5
% 2.58/1.37  #Chain   : 0
% 2.58/1.37  #Close   : 0
% 2.58/1.37  
% 2.58/1.37  Ordering : KBO
% 2.58/1.37  
% 2.58/1.37  Simplification rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Subsume      : 10
% 2.58/1.37  #Demod        : 8
% 2.58/1.37  #Tautology    : 17
% 2.58/1.37  #SimpNegUnit  : 0
% 2.58/1.37  #BackRed      : 0
% 2.58/1.37  
% 2.58/1.37  #Partial instantiations: 0
% 2.58/1.37  #Strategies tried      : 1
% 2.58/1.37  
% 2.58/1.37  Timing (in seconds)
% 2.58/1.37  ----------------------
% 2.58/1.37  Preprocessing        : 0.31
% 2.58/1.37  Parsing              : 0.18
% 2.58/1.37  CNF conversion       : 0.02
% 2.58/1.37  Main loop            : 0.29
% 2.58/1.37  Inferencing          : 0.13
% 2.58/1.37  Reduction            : 0.07
% 2.58/1.37  Demodulation         : 0.05
% 2.58/1.37  BG Simplification    : 0.02
% 2.58/1.37  Subsumption          : 0.06
% 2.58/1.37  Abstraction          : 0.01
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.38  Cooper               : 0.00
% 2.58/1.38  Total                : 0.64
% 2.58/1.38  Index Insertion      : 0.00
% 2.58/1.38  Index Deletion       : 0.00
% 2.58/1.38  Index Matching       : 0.00
% 2.58/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
