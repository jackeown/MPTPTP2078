%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:03 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 118 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 180 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_88,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_42,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_179,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_185,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_179])).

tff(c_189,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_185])).

tff(c_282,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_291,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_282])).

tff(c_38,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_516,plain,(
    ! [A_133,B_134,C_135] :
      ( r1_tarski(A_133,k2_xboole_0(B_134,C_135))
      | ~ r1_tarski(k4_xboole_0(A_133,B_134),C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_539,plain,(
    ! [A_136,B_137] : r1_tarski(A_136,k2_xboole_0(B_137,A_136)) ),
    inference(resolution,[status(thm)],[c_10,c_516])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_571,plain,(
    ! [A_3,B_137,A_136] :
      ( r1_tarski(A_3,k2_xboole_0(B_137,A_136))
      | ~ r1_tarski(A_3,A_136) ) ),
    inference(resolution,[status(thm)],[c_539,c_8])).

tff(c_424,plain,(
    ! [C_107,A_108,B_109] :
      ( v4_relat_1(C_107,A_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_433,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_424])).

tff(c_34,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_relat_1(B_29),A_28)
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_122,plain,(
    ! [B_53,A_54] : k3_tarski(k2_tarski(B_53,A_54)) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_98])).

tff(c_20,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_20])).

tff(c_1160,plain,(
    ! [A_181,B_182,A_183] :
      ( r1_tarski(A_181,k2_xboole_0(B_182,A_183))
      | ~ r1_tarski(A_181,A_183) ) ),
    inference(resolution,[status(thm)],[c_539,c_8])).

tff(c_1199,plain,(
    ! [A_181,A_54,B_53] :
      ( r1_tarski(A_181,k2_xboole_0(A_54,B_53))
      | ~ r1_tarski(A_181,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_1160])).

tff(c_40,plain,(
    ! [A_32] :
      ( k2_xboole_0(k1_relat_1(A_32),k2_relat_1(A_32)) = k3_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_659,plain,(
    ! [A_147,C_148,B_149] :
      ( r1_tarski(k2_xboole_0(A_147,C_148),B_149)
      | ~ r1_tarski(C_148,B_149)
      | ~ r1_tarski(A_147,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2609,plain,(
    ! [A_285,B_286] :
      ( r1_tarski(k3_relat_1(A_285),B_286)
      | ~ r1_tarski(k2_relat_1(A_285),B_286)
      | ~ r1_tarski(k1_relat_1(A_285),B_286)
      | ~ v1_relat_1(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_659])).

tff(c_48,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2664,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2609,c_48])).

tff(c_2687,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_2664])).

tff(c_3242,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2687])).

tff(c_3253,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1199,c_3242])).

tff(c_3266,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_3253])).

tff(c_3270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_433,c_3266])).

tff(c_3271,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2687])).

tff(c_3423,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_571,c_3271])).

tff(c_3429,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_3423])).

tff(c_3433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_291,c_3429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:36:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.90  
% 4.70/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.90  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.70/1.90  
% 4.70/1.90  %Foreground sorts:
% 4.70/1.90  
% 4.70/1.90  
% 4.70/1.90  %Background operators:
% 4.70/1.90  
% 4.70/1.90  
% 4.70/1.90  %Foreground operators:
% 4.70/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.70/1.90  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.70/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.70/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.70/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.70/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.70/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.70/1.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.70/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.70/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.70/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.70/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.70/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.90  
% 4.70/1.91  tff(f_88, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.70/1.91  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 4.70/1.91  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.70/1.91  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.70/1.91  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.70/1.91  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.70/1.91  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 4.70/1.91  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.70/1.91  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.70/1.91  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.70/1.91  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.70/1.91  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 4.70/1.91  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.70/1.91  tff(c_42, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.70/1.91  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.70/1.91  tff(c_179, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.70/1.91  tff(c_185, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_179])).
% 4.70/1.91  tff(c_189, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_185])).
% 4.70/1.91  tff(c_282, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.70/1.91  tff(c_291, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_282])).
% 4.70/1.91  tff(c_38, plain, (![B_31, A_30]: (r1_tarski(k2_relat_1(B_31), A_30) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.70/1.91  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.70/1.91  tff(c_516, plain, (![A_133, B_134, C_135]: (r1_tarski(A_133, k2_xboole_0(B_134, C_135)) | ~r1_tarski(k4_xboole_0(A_133, B_134), C_135))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.70/1.91  tff(c_539, plain, (![A_136, B_137]: (r1_tarski(A_136, k2_xboole_0(B_137, A_136)))), inference(resolution, [status(thm)], [c_10, c_516])).
% 4.70/1.91  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.91  tff(c_571, plain, (![A_3, B_137, A_136]: (r1_tarski(A_3, k2_xboole_0(B_137, A_136)) | ~r1_tarski(A_3, A_136))), inference(resolution, [status(thm)], [c_539, c_8])).
% 4.70/1.91  tff(c_424, plain, (![C_107, A_108, B_109]: (v4_relat_1(C_107, A_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.70/1.91  tff(c_433, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_424])).
% 4.70/1.91  tff(c_34, plain, (![B_29, A_28]: (r1_tarski(k1_relat_1(B_29), A_28) | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.70/1.91  tff(c_16, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.70/1.91  tff(c_98, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.70/1.91  tff(c_122, plain, (![B_53, A_54]: (k3_tarski(k2_tarski(B_53, A_54))=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_16, c_98])).
% 4.70/1.91  tff(c_20, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.70/1.91  tff(c_128, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_122, c_20])).
% 4.70/1.91  tff(c_1160, plain, (![A_181, B_182, A_183]: (r1_tarski(A_181, k2_xboole_0(B_182, A_183)) | ~r1_tarski(A_181, A_183))), inference(resolution, [status(thm)], [c_539, c_8])).
% 4.70/1.91  tff(c_1199, plain, (![A_181, A_54, B_53]: (r1_tarski(A_181, k2_xboole_0(A_54, B_53)) | ~r1_tarski(A_181, A_54))), inference(superposition, [status(thm), theory('equality')], [c_128, c_1160])).
% 4.70/1.91  tff(c_40, plain, (![A_32]: (k2_xboole_0(k1_relat_1(A_32), k2_relat_1(A_32))=k3_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.70/1.91  tff(c_659, plain, (![A_147, C_148, B_149]: (r1_tarski(k2_xboole_0(A_147, C_148), B_149) | ~r1_tarski(C_148, B_149) | ~r1_tarski(A_147, B_149))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.70/1.91  tff(c_2609, plain, (![A_285, B_286]: (r1_tarski(k3_relat_1(A_285), B_286) | ~r1_tarski(k2_relat_1(A_285), B_286) | ~r1_tarski(k1_relat_1(A_285), B_286) | ~v1_relat_1(A_285))), inference(superposition, [status(thm), theory('equality')], [c_40, c_659])).
% 4.70/1.91  tff(c_48, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.70/1.91  tff(c_2664, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2609, c_48])).
% 4.70/1.91  tff(c_2687, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_2664])).
% 4.70/1.91  tff(c_3242, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2687])).
% 4.70/1.91  tff(c_3253, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1199, c_3242])).
% 4.70/1.91  tff(c_3266, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_3253])).
% 4.70/1.91  tff(c_3270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_433, c_3266])).
% 4.70/1.91  tff(c_3271, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2687])).
% 4.70/1.91  tff(c_3423, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_571, c_3271])).
% 4.70/1.91  tff(c_3429, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_3423])).
% 4.70/1.91  tff(c_3433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_291, c_3429])).
% 4.70/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.91  
% 4.70/1.91  Inference rules
% 4.70/1.91  ----------------------
% 4.70/1.91  #Ref     : 0
% 4.70/1.91  #Sup     : 851
% 4.70/1.91  #Fact    : 0
% 4.70/1.91  #Define  : 0
% 4.70/1.91  #Split   : 2
% 4.70/1.91  #Chain   : 0
% 4.70/1.91  #Close   : 0
% 4.70/1.91  
% 4.70/1.91  Ordering : KBO
% 4.70/1.91  
% 4.70/1.91  Simplification rules
% 4.70/1.91  ----------------------
% 4.70/1.91  #Subsume      : 125
% 4.70/1.91  #Demod        : 198
% 4.70/1.91  #Tautology    : 205
% 4.70/1.91  #SimpNegUnit  : 0
% 4.70/1.91  #BackRed      : 2
% 4.70/1.91  
% 4.70/1.91  #Partial instantiations: 0
% 4.70/1.91  #Strategies tried      : 1
% 4.70/1.91  
% 4.70/1.91  Timing (in seconds)
% 4.70/1.91  ----------------------
% 4.70/1.92  Preprocessing        : 0.33
% 4.70/1.92  Parsing              : 0.18
% 4.70/1.92  CNF conversion       : 0.02
% 4.70/1.92  Main loop            : 0.82
% 4.70/1.92  Inferencing          : 0.27
% 4.70/1.92  Reduction            : 0.29
% 4.70/1.92  Demodulation         : 0.23
% 4.70/1.92  BG Simplification    : 0.03
% 4.70/1.92  Subsumption          : 0.16
% 4.70/1.92  Abstraction          : 0.04
% 4.70/1.92  MUC search           : 0.00
% 4.70/1.92  Cooper               : 0.00
% 4.70/1.92  Total                : 1.18
% 4.70/1.92  Index Insertion      : 0.00
% 4.70/1.92  Index Deletion       : 0.00
% 4.70/1.92  Index Matching       : 0.00
% 4.70/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
