%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:32 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 110 expanded)
%              Number of leaves         :   40 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 206 expanded)
%              Number of equality atoms :   76 ( 111 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_70,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_212,plain,(
    ! [A_98,D_100,B_99,C_97,E_101] : k4_enumset1(A_98,A_98,B_99,C_97,D_100,E_101) = k3_enumset1(A_98,B_99,C_97,D_100,E_101) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [H_25,C_18,B_17,D_19,E_20,F_21] : r2_hidden(H_25,k4_enumset1(H_25,B_17,C_18,D_19,E_20,F_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_273,plain,(
    ! [A_112,B_110,C_111,D_113,E_109] : r2_hidden(A_112,k3_enumset1(A_112,B_110,C_111,D_113,E_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_24])).

tff(c_277,plain,(
    ! [A_114,B_115,C_116,D_117] : r2_hidden(A_114,k2_enumset1(A_114,B_115,C_116,D_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_273])).

tff(c_281,plain,(
    ! [A_118,B_119,C_120] : r2_hidden(A_118,k1_enumset1(A_118,B_119,C_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_277])).

tff(c_285,plain,(
    ! [A_121,B_122] : r2_hidden(A_121,k2_tarski(A_121,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_281])).

tff(c_288,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_285])).

tff(c_60,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_117,plain,(
    ! [A_42] :
      ( k10_relat_1(A_42,k2_relat_1(A_42)) = k1_relat_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_126,plain,(
    ! [A_27] :
      ( k10_relat_1(k6_relat_1(A_27),A_27) = k1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_117])).

tff(c_130,plain,(
    ! [A_27] : k10_relat_1(k6_relat_1(A_27),A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_126])).

tff(c_155,plain,(
    ! [B_83,A_84] :
      ( k10_relat_1(B_83,k1_tarski(A_84)) != k1_xboole_0
      | ~ r2_hidden(A_84,k2_relat_1(B_83))
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_158,plain,(
    ! [A_27,A_84] :
      ( k10_relat_1(k6_relat_1(A_27),k1_tarski(A_84)) != k1_xboole_0
      | ~ r2_hidden(A_84,A_27)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_155])).

tff(c_161,plain,(
    ! [A_85,A_86] :
      ( k10_relat_1(k6_relat_1(A_85),k1_tarski(A_86)) != k1_xboole_0
      | ~ r2_hidden(A_86,A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_158])).

tff(c_165,plain,(
    ! [A_86] :
      ( k1_tarski(A_86) != k1_xboole_0
      | ~ r2_hidden(A_86,k1_tarski(A_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_161])).

tff(c_291,plain,(
    ! [A_86] : k1_tarski(A_86) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_165])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_293,plain,(
    ! [D_124,C_125,B_126,A_127] :
      ( r2_hidden(k1_funct_1(D_124,C_125),B_126)
      | k1_xboole_0 = B_126
      | ~ r2_hidden(C_125,A_127)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(D_124,A_127,B_126)
      | ~ v1_funct_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_348,plain,(
    ! [D_138,B_139] :
      ( r2_hidden(k1_funct_1(D_138,'#skF_5'),B_139)
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_139)))
      | ~ v1_funct_2(D_138,'#skF_3',B_139)
      | ~ v1_funct_1(D_138) ) ),
    inference(resolution,[status(thm)],[c_72,c_293])).

tff(c_351,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_348])).

tff(c_354,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_351])).

tff(c_355,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_354])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_239,plain,(
    ! [H_106,E_104,C_108,F_102,B_103,A_105,D_107] :
      ( H_106 = F_102
      | H_106 = E_104
      | H_106 = D_107
      | H_106 = C_108
      | H_106 = B_103
      | H_106 = A_105
      | ~ r2_hidden(H_106,k4_enumset1(A_105,B_103,C_108,D_107,E_104,F_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_427,plain,(
    ! [B_183,D_184,E_185,A_182,C_180,H_181] :
      ( H_181 = E_185
      | H_181 = D_184
      | H_181 = C_180
      | H_181 = B_183
      | H_181 = A_182
      | H_181 = A_182
      | ~ r2_hidden(H_181,k3_enumset1(A_182,B_183,C_180,D_184,E_185)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_239])).

tff(c_456,plain,(
    ! [H_187,B_188,A_190,D_186,C_189] :
      ( H_187 = D_186
      | H_187 = C_189
      | H_187 = B_188
      | H_187 = A_190
      | H_187 = A_190
      | H_187 = A_190
      | ~ r2_hidden(H_187,k2_enumset1(A_190,B_188,C_189,D_186)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_427])).

tff(c_480,plain,(
    ! [H_191,C_192,B_193,A_194] :
      ( H_191 = C_192
      | H_191 = B_193
      | H_191 = A_194
      | H_191 = A_194
      | H_191 = A_194
      | H_191 = A_194
      | ~ r2_hidden(H_191,k1_enumset1(A_194,B_193,C_192)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_456])).

tff(c_505,plain,(
    ! [H_202,B_203,A_204] :
      ( H_202 = B_203
      | H_202 = A_204
      | H_202 = A_204
      | H_202 = A_204
      | H_202 = A_204
      | H_202 = A_204
      | ~ r2_hidden(H_202,k2_tarski(A_204,B_203)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_480])).

tff(c_519,plain,(
    ! [H_205,A_206] :
      ( H_205 = A_206
      | H_205 = A_206
      | H_205 = A_206
      | H_205 = A_206
      | H_205 = A_206
      | H_205 = A_206
      | ~ r2_hidden(H_205,k1_tarski(A_206)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_505])).

tff(c_522,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_355,c_519])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_70,c_70,c_70,c_70,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 21:04:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.40  
% 2.97/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.97/1.41  
% 2.97/1.41  %Foreground sorts:
% 2.97/1.41  
% 2.97/1.41  
% 2.97/1.41  %Background operators:
% 2.97/1.41  
% 2.97/1.41  
% 2.97/1.41  %Foreground operators:
% 2.97/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.97/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.97/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.97/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.97/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.97/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.41  
% 2.97/1.42  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.97/1.42  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.97/1.42  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.97/1.42  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.97/1.42  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.97/1.42  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.97/1.42  tff(f_59, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 2.97/1.42  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.97/1.42  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.97/1.42  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.97/1.42  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.97/1.42  tff(f_90, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.97/1.42  tff(c_70, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.97/1.42  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.42  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.42  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.42  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.42  tff(c_212, plain, (![A_98, D_100, B_99, C_97, E_101]: (k4_enumset1(A_98, A_98, B_99, C_97, D_100, E_101)=k3_enumset1(A_98, B_99, C_97, D_100, E_101))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.42  tff(c_24, plain, (![H_25, C_18, B_17, D_19, E_20, F_21]: (r2_hidden(H_25, k4_enumset1(H_25, B_17, C_18, D_19, E_20, F_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.97/1.42  tff(c_273, plain, (![A_112, B_110, C_111, D_113, E_109]: (r2_hidden(A_112, k3_enumset1(A_112, B_110, C_111, D_113, E_109)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_24])).
% 2.97/1.42  tff(c_277, plain, (![A_114, B_115, C_116, D_117]: (r2_hidden(A_114, k2_enumset1(A_114, B_115, C_116, D_117)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_273])).
% 2.97/1.42  tff(c_281, plain, (![A_118, B_119, C_120]: (r2_hidden(A_118, k1_enumset1(A_118, B_119, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_277])).
% 2.97/1.42  tff(c_285, plain, (![A_121, B_122]: (r2_hidden(A_121, k2_tarski(A_121, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_281])).
% 2.97/1.42  tff(c_288, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_285])).
% 2.97/1.42  tff(c_60, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.42  tff(c_56, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.42  tff(c_58, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.42  tff(c_117, plain, (![A_42]: (k10_relat_1(A_42, k2_relat_1(A_42))=k1_relat_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.42  tff(c_126, plain, (![A_27]: (k10_relat_1(k6_relat_1(A_27), A_27)=k1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_117])).
% 2.97/1.42  tff(c_130, plain, (![A_27]: (k10_relat_1(k6_relat_1(A_27), A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_126])).
% 2.97/1.42  tff(c_155, plain, (![B_83, A_84]: (k10_relat_1(B_83, k1_tarski(A_84))!=k1_xboole_0 | ~r2_hidden(A_84, k2_relat_1(B_83)) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.97/1.42  tff(c_158, plain, (![A_27, A_84]: (k10_relat_1(k6_relat_1(A_27), k1_tarski(A_84))!=k1_xboole_0 | ~r2_hidden(A_84, A_27) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_155])).
% 2.97/1.42  tff(c_161, plain, (![A_85, A_86]: (k10_relat_1(k6_relat_1(A_85), k1_tarski(A_86))!=k1_xboole_0 | ~r2_hidden(A_86, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_158])).
% 2.97/1.42  tff(c_165, plain, (![A_86]: (k1_tarski(A_86)!=k1_xboole_0 | ~r2_hidden(A_86, k1_tarski(A_86)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_161])).
% 2.97/1.42  tff(c_291, plain, (![A_86]: (k1_tarski(A_86)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_288, c_165])).
% 2.97/1.42  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.97/1.42  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.97/1.42  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.97/1.42  tff(c_72, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.97/1.42  tff(c_293, plain, (![D_124, C_125, B_126, A_127]: (r2_hidden(k1_funct_1(D_124, C_125), B_126) | k1_xboole_0=B_126 | ~r2_hidden(C_125, A_127) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(D_124, A_127, B_126) | ~v1_funct_1(D_124))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.42  tff(c_348, plain, (![D_138, B_139]: (r2_hidden(k1_funct_1(D_138, '#skF_5'), B_139) | k1_xboole_0=B_139 | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_139))) | ~v1_funct_2(D_138, '#skF_3', B_139) | ~v1_funct_1(D_138))), inference(resolution, [status(thm)], [c_72, c_293])).
% 2.97/1.42  tff(c_351, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_348])).
% 2.97/1.42  tff(c_354, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_351])).
% 2.97/1.42  tff(c_355, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_291, c_354])).
% 2.97/1.42  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.42  tff(c_239, plain, (![H_106, E_104, C_108, F_102, B_103, A_105, D_107]: (H_106=F_102 | H_106=E_104 | H_106=D_107 | H_106=C_108 | H_106=B_103 | H_106=A_105 | ~r2_hidden(H_106, k4_enumset1(A_105, B_103, C_108, D_107, E_104, F_102)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.97/1.42  tff(c_427, plain, (![B_183, D_184, E_185, A_182, C_180, H_181]: (H_181=E_185 | H_181=D_184 | H_181=C_180 | H_181=B_183 | H_181=A_182 | H_181=A_182 | ~r2_hidden(H_181, k3_enumset1(A_182, B_183, C_180, D_184, E_185)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_239])).
% 2.97/1.42  tff(c_456, plain, (![H_187, B_188, A_190, D_186, C_189]: (H_187=D_186 | H_187=C_189 | H_187=B_188 | H_187=A_190 | H_187=A_190 | H_187=A_190 | ~r2_hidden(H_187, k2_enumset1(A_190, B_188, C_189, D_186)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_427])).
% 2.97/1.42  tff(c_480, plain, (![H_191, C_192, B_193, A_194]: (H_191=C_192 | H_191=B_193 | H_191=A_194 | H_191=A_194 | H_191=A_194 | H_191=A_194 | ~r2_hidden(H_191, k1_enumset1(A_194, B_193, C_192)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_456])).
% 2.97/1.42  tff(c_505, plain, (![H_202, B_203, A_204]: (H_202=B_203 | H_202=A_204 | H_202=A_204 | H_202=A_204 | H_202=A_204 | H_202=A_204 | ~r2_hidden(H_202, k2_tarski(A_204, B_203)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_480])).
% 2.97/1.42  tff(c_519, plain, (![H_205, A_206]: (H_205=A_206 | H_205=A_206 | H_205=A_206 | H_205=A_206 | H_205=A_206 | H_205=A_206 | ~r2_hidden(H_205, k1_tarski(A_206)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_505])).
% 2.97/1.42  tff(c_522, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_355, c_519])).
% 2.97/1.42  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_70, c_70, c_70, c_70, c_522])).
% 2.97/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.42  
% 2.97/1.42  Inference rules
% 2.97/1.42  ----------------------
% 2.97/1.42  #Ref     : 0
% 2.97/1.42  #Sup     : 103
% 2.97/1.42  #Fact    : 0
% 2.97/1.42  #Define  : 0
% 2.97/1.42  #Split   : 0
% 2.97/1.42  #Chain   : 0
% 2.97/1.42  #Close   : 0
% 2.97/1.42  
% 2.97/1.42  Ordering : KBO
% 2.97/1.42  
% 2.97/1.42  Simplification rules
% 2.97/1.42  ----------------------
% 2.97/1.42  #Subsume      : 1
% 2.97/1.42  #Demod        : 13
% 2.97/1.42  #Tautology    : 49
% 2.97/1.42  #SimpNegUnit  : 2
% 2.97/1.42  #BackRed      : 1
% 2.97/1.42  
% 2.97/1.42  #Partial instantiations: 0
% 2.97/1.42  #Strategies tried      : 1
% 2.97/1.42  
% 2.97/1.42  Timing (in seconds)
% 2.97/1.42  ----------------------
% 2.97/1.43  Preprocessing        : 0.34
% 2.97/1.43  Parsing              : 0.17
% 2.97/1.43  CNF conversion       : 0.03
% 2.97/1.43  Main loop            : 0.33
% 2.97/1.43  Inferencing          : 0.11
% 2.97/1.43  Reduction            : 0.10
% 2.97/1.43  Demodulation         : 0.07
% 2.97/1.43  BG Simplification    : 0.02
% 2.97/1.43  Subsumption          : 0.08
% 2.97/1.43  Abstraction          : 0.03
% 2.97/1.43  MUC search           : 0.00
% 2.97/1.43  Cooper               : 0.00
% 2.97/1.43  Total                : 0.71
% 2.97/1.43  Index Insertion      : 0.00
% 2.97/1.43  Index Deletion       : 0.00
% 2.97/1.43  Index Matching       : 0.00
% 2.97/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
