%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:23 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 257 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   21
%              Number of atoms          :  115 ( 428 expanded)
%              Number of equality atoms :   34 ( 140 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_56,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_611,plain,(
    ! [A_142,B_143,C_144] :
      ( ~ r2_hidden('#skF_2'(A_142,B_143,C_144),B_143)
      | r2_hidden('#skF_3'(A_142,B_143,C_144),C_144)
      | k4_xboole_0(A_142,B_143) = C_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_618,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_611])).

tff(c_620,plain,(
    ! [A_145,C_146] :
      ( r2_hidden('#skF_3'(A_145,A_145,C_146),C_146)
      | k4_xboole_0(A_145,A_145) = C_146 ) ),
    inference(resolution,[status(thm)],[c_24,c_611])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_98])).

tff(c_36,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_120,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_133,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_152,plain,(
    ! [B_74] : k3_xboole_0(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_176,plain,(
    ! [B_75] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_34])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_182,plain,(
    ! [D_11,B_75] :
      ( ~ r2_hidden(D_11,B_75)
      | ~ r2_hidden(D_11,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_10])).

tff(c_254,plain,(
    ! [D_83,B_84] :
      ( ~ r2_hidden(D_83,B_84)
      | ~ r2_hidden(D_83,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_182])).

tff(c_322,plain,(
    ! [A_99,B_100] :
      ( ~ r2_hidden('#skF_1'(A_99,B_100),k4_xboole_0(k1_xboole_0,k1_xboole_0))
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_336,plain,(
    ! [B_101] : r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),B_101) ),
    inference(resolution,[status(thm)],[c_6,c_322])).

tff(c_128,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_352,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_336,c_128])).

tff(c_157,plain,(
    ! [B_74] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_34])).

tff(c_179,plain,(
    ! [B_75,B_74] : k4_xboole_0(k1_xboole_0,B_75) = k4_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_157])).

tff(c_365,plain,(
    ! [B_74] : k4_xboole_0(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_179])).

tff(c_195,plain,(
    ! [B_77,B_76] : k4_xboole_0(k1_xboole_0,B_77) = k4_xboole_0(k1_xboole_0,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_157])).

tff(c_210,plain,(
    ! [D_11,B_76,B_77] :
      ( ~ r2_hidden(D_11,B_76)
      | ~ r2_hidden(D_11,k4_xboole_0(k1_xboole_0,B_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_10])).

tff(c_379,plain,(
    ! [D_11,B_76] :
      ( ~ r2_hidden(D_11,B_76)
      | ~ r2_hidden(D_11,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_210])).

tff(c_647,plain,(
    ! [A_147,C_148] :
      ( ~ r2_hidden('#skF_3'(A_147,A_147,C_148),k1_xboole_0)
      | k4_xboole_0(A_147,A_147) = C_148 ) ),
    inference(resolution,[status(thm)],[c_620,c_379])).

tff(c_658,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_618,c_647])).

tff(c_663,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_107])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_421,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(A_108,B_107)
      | ~ v1_zfmisc_1(B_107)
      | v1_xboole_0(B_107)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1010,plain,(
    ! [A_189,B_190] :
      ( k3_xboole_0(A_189,B_190) = A_189
      | ~ v1_zfmisc_1(A_189)
      | v1_xboole_0(A_189)
      | v1_xboole_0(k3_xboole_0(A_189,B_190)) ) ),
    inference(resolution,[status(thm)],[c_36,c_421])).

tff(c_58,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1013,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1010,c_58])).

tff(c_1022,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1013])).

tff(c_1023,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1022])).

tff(c_1036,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_34])).

tff(c_1047,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_1036])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k4_xboole_0(A_6,B_7))
      | r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1083,plain,(
    ! [D_191] :
      ( r2_hidden(D_191,k1_xboole_0)
      | r2_hidden(D_191,'#skF_5')
      | ~ r2_hidden(D_191,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_8])).

tff(c_664,plain,(
    ! [A_149] : k4_xboole_0(A_149,A_149) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_618,c_647])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_675,plain,(
    ! [D_11,A_149] :
      ( r2_hidden(D_11,A_149)
      | ~ r2_hidden(D_11,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_12])).

tff(c_1124,plain,(
    ! [D_191,A_149] :
      ( r2_hidden(D_191,A_149)
      | r2_hidden(D_191,'#skF_5')
      | ~ r2_hidden(D_191,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1083,c_675])).

tff(c_1240,plain,(
    ! [D_194] :
      ( ~ r2_hidden(D_194,'#skF_4')
      | r2_hidden(D_194,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1124])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1345,plain,(
    ! [A_200] :
      ( r1_tarski(A_200,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_200,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1240,c_4])).

tff(c_1357,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1345])).

tff(c_1363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_1357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:59:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.59  
% 3.31/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.60  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.31/1.60  
% 3.31/1.60  %Foreground sorts:
% 3.31/1.60  
% 3.31/1.60  
% 3.31/1.60  %Background operators:
% 3.31/1.60  
% 3.31/1.60  
% 3.31/1.60  %Foreground operators:
% 3.31/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.31/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.31/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.31/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.31/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.60  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.31/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.31/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.31/1.60  
% 3.31/1.61  tff(f_95, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 3.31/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.61  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.31/1.61  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.31/1.61  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.31/1.61  tff(f_54, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.31/1.61  tff(f_56, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.31/1.61  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.31/1.61  tff(f_83, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.31/1.61  tff(c_56, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.31/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.61  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.61  tff(c_611, plain, (![A_142, B_143, C_144]: (~r2_hidden('#skF_2'(A_142, B_143, C_144), B_143) | r2_hidden('#skF_3'(A_142, B_143, C_144), C_144) | k4_xboole_0(A_142, B_143)=C_144)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.61  tff(c_618, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_611])).
% 3.31/1.61  tff(c_620, plain, (![A_145, C_146]: (r2_hidden('#skF_3'(A_145, A_145, C_146), C_146) | k4_xboole_0(A_145, A_145)=C_146)), inference(resolution, [status(thm)], [c_24, c_611])).
% 3.31/1.61  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.31/1.61  tff(c_98, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.31/1.61  tff(c_107, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_98])).
% 3.31/1.61  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.61  tff(c_38, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.61  tff(c_120, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.61  tff(c_133, plain, (![A_71]: (k1_xboole_0=A_71 | ~r1_tarski(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_120])).
% 3.31/1.61  tff(c_152, plain, (![B_74]: (k3_xboole_0(k1_xboole_0, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_133])).
% 3.31/1.61  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.31/1.61  tff(c_176, plain, (![B_75]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_75))), inference(superposition, [status(thm), theory('equality')], [c_152, c_34])).
% 3.31/1.61  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.61  tff(c_182, plain, (![D_11, B_75]: (~r2_hidden(D_11, B_75) | ~r2_hidden(D_11, k5_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_10])).
% 3.31/1.61  tff(c_254, plain, (![D_83, B_84]: (~r2_hidden(D_83, B_84) | ~r2_hidden(D_83, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_182])).
% 3.31/1.61  tff(c_322, plain, (![A_99, B_100]: (~r2_hidden('#skF_1'(A_99, B_100), k4_xboole_0(k1_xboole_0, k1_xboole_0)) | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_6, c_254])).
% 3.31/1.61  tff(c_336, plain, (![B_101]: (r1_tarski(k4_xboole_0(k1_xboole_0, k1_xboole_0), B_101))), inference(resolution, [status(thm)], [c_6, c_322])).
% 3.31/1.61  tff(c_128, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_120])).
% 3.31/1.61  tff(c_352, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_336, c_128])).
% 3.31/1.61  tff(c_157, plain, (![B_74]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_152, c_34])).
% 3.31/1.61  tff(c_179, plain, (![B_75, B_74]: (k4_xboole_0(k1_xboole_0, B_75)=k4_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_176, c_157])).
% 3.31/1.61  tff(c_365, plain, (![B_74]: (k4_xboole_0(k1_xboole_0, B_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_352, c_179])).
% 3.31/1.61  tff(c_195, plain, (![B_77, B_76]: (k4_xboole_0(k1_xboole_0, B_77)=k4_xboole_0(k1_xboole_0, B_76))), inference(superposition, [status(thm), theory('equality')], [c_176, c_157])).
% 3.31/1.61  tff(c_210, plain, (![D_11, B_76, B_77]: (~r2_hidden(D_11, B_76) | ~r2_hidden(D_11, k4_xboole_0(k1_xboole_0, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_195, c_10])).
% 3.31/1.61  tff(c_379, plain, (![D_11, B_76]: (~r2_hidden(D_11, B_76) | ~r2_hidden(D_11, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_210])).
% 3.31/1.61  tff(c_647, plain, (![A_147, C_148]: (~r2_hidden('#skF_3'(A_147, A_147, C_148), k1_xboole_0) | k4_xboole_0(A_147, A_147)=C_148)), inference(resolution, [status(thm)], [c_620, c_379])).
% 3.31/1.61  tff(c_658, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_618, c_647])).
% 3.31/1.61  tff(c_663, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_658, c_107])).
% 3.31/1.61  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.31/1.61  tff(c_60, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.31/1.61  tff(c_421, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(A_108, B_107) | ~v1_zfmisc_1(B_107) | v1_xboole_0(B_107) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.31/1.61  tff(c_1010, plain, (![A_189, B_190]: (k3_xboole_0(A_189, B_190)=A_189 | ~v1_zfmisc_1(A_189) | v1_xboole_0(A_189) | v1_xboole_0(k3_xboole_0(A_189, B_190)))), inference(resolution, [status(thm)], [c_36, c_421])).
% 3.31/1.61  tff(c_58, plain, (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.31/1.61  tff(c_1013, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1010, c_58])).
% 3.31/1.61  tff(c_1022, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1013])).
% 3.31/1.61  tff(c_1023, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_1022])).
% 3.31/1.61  tff(c_1036, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1023, c_34])).
% 3.31/1.61  tff(c_1047, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_663, c_1036])).
% 3.31/1.61  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k4_xboole_0(A_6, B_7)) | r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.61  tff(c_1083, plain, (![D_191]: (r2_hidden(D_191, k1_xboole_0) | r2_hidden(D_191, '#skF_5') | ~r2_hidden(D_191, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1047, c_8])).
% 3.31/1.61  tff(c_664, plain, (![A_149]: (k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_618, c_647])).
% 3.31/1.61  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.61  tff(c_675, plain, (![D_11, A_149]: (r2_hidden(D_11, A_149) | ~r2_hidden(D_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_664, c_12])).
% 3.31/1.61  tff(c_1124, plain, (![D_191, A_149]: (r2_hidden(D_191, A_149) | r2_hidden(D_191, '#skF_5') | ~r2_hidden(D_191, '#skF_4'))), inference(resolution, [status(thm)], [c_1083, c_675])).
% 3.31/1.61  tff(c_1240, plain, (![D_194]: (~r2_hidden(D_194, '#skF_4') | r2_hidden(D_194, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_1124])).
% 3.31/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.61  tff(c_1345, plain, (![A_200]: (r1_tarski(A_200, '#skF_5') | ~r2_hidden('#skF_1'(A_200, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_1240, c_4])).
% 3.31/1.61  tff(c_1357, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_1345])).
% 3.31/1.61  tff(c_1363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_1357])).
% 3.31/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.61  
% 3.31/1.61  Inference rules
% 3.31/1.61  ----------------------
% 3.31/1.61  #Ref     : 0
% 3.31/1.61  #Sup     : 294
% 3.31/1.61  #Fact    : 2
% 3.31/1.61  #Define  : 0
% 3.31/1.61  #Split   : 1
% 3.31/1.61  #Chain   : 0
% 3.31/1.61  #Close   : 0
% 3.31/1.61  
% 3.31/1.61  Ordering : KBO
% 3.31/1.61  
% 3.31/1.61  Simplification rules
% 3.31/1.61  ----------------------
% 3.31/1.61  #Subsume      : 65
% 3.31/1.61  #Demod        : 135
% 3.31/1.61  #Tautology    : 122
% 3.31/1.61  #SimpNegUnit  : 3
% 3.31/1.61  #BackRed      : 8
% 3.31/1.61  
% 3.31/1.61  #Partial instantiations: 0
% 3.31/1.61  #Strategies tried      : 1
% 3.31/1.61  
% 3.31/1.61  Timing (in seconds)
% 3.31/1.61  ----------------------
% 3.31/1.62  Preprocessing        : 0.34
% 3.31/1.62  Parsing              : 0.17
% 3.31/1.62  CNF conversion       : 0.03
% 3.31/1.62  Main loop            : 0.45
% 3.31/1.62  Inferencing          : 0.17
% 3.31/1.62  Reduction            : 0.13
% 3.31/1.62  Demodulation         : 0.10
% 3.31/1.62  BG Simplification    : 0.02
% 3.31/1.62  Subsumption          : 0.09
% 3.31/1.62  Abstraction          : 0.03
% 3.31/1.62  MUC search           : 0.00
% 3.31/1.62  Cooper               : 0.00
% 3.31/1.62  Total                : 0.83
% 3.31/1.62  Index Insertion      : 0.00
% 3.31/1.62  Index Deletion       : 0.00
% 3.31/1.62  Index Matching       : 0.00
% 3.31/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
