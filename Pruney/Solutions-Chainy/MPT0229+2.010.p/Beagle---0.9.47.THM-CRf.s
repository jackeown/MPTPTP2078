%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:54 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 163 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :   71 ( 195 expanded)
%              Number of equality atoms :   52 ( 135 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_68,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),k1_tarski(B_29)) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(B_79,A_80)
      | ~ r1_xboole_0(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [B_15,A_14] : r1_xboole_0(B_15,k4_xboole_0(A_14,B_15)) ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_120,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = k1_xboole_0
      | ~ r1_xboole_0(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [B_15,A_14] : k3_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_120])).

tff(c_188,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [B_15,A_14] : k4_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k5_xboole_0(B_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_188])).

tff(c_209,plain,(
    ! [B_15,A_14] : k4_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = B_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_197])).

tff(c_424,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k3_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_458,plain,(
    ! [B_15,A_14] : k3_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_424])).

tff(c_469,plain,(
    ! [B_15] : k4_xboole_0(B_15,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_458])).

tff(c_70,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_111,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_111])).

tff(c_200,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_188])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_188])).

tff(c_330,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_206])).

tff(c_518,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_330])).

tff(c_633,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k4_xboole_0(B_121,A_120)) = k2_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_645,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_633])).

tff(c_657,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_645])).

tff(c_1002,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_48])).

tff(c_1186,plain,(
    ! [A_140,B_141,C_142] : k2_xboole_0(k1_tarski(A_140),k2_tarski(B_141,C_142)) = k1_enumset1(A_140,B_141,C_142) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1195,plain,(
    ! [A_140] : k2_xboole_0(k1_tarski(A_140),k1_tarski('#skF_4')) = k1_enumset1(A_140,'#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_1186])).

tff(c_1258,plain,(
    ! [A_145] : k1_enumset1(A_145,'#skF_4','#skF_3') = k2_tarski(A_145,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1195])).

tff(c_24,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1280,plain,(
    ! [A_145] : r2_hidden('#skF_3',k2_tarski(A_145,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1258,c_24])).

tff(c_56,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1563,plain,(
    ! [E_159,C_160,B_161,A_162] :
      ( E_159 = C_160
      | E_159 = B_161
      | E_159 = A_162
      | ~ r2_hidden(E_159,k1_enumset1(A_162,B_161,C_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4941,plain,(
    ! [E_287,B_288,A_289] :
      ( E_287 = B_288
      | E_287 = A_289
      | E_287 = A_289
      | ~ r2_hidden(E_287,k2_tarski(A_289,B_288)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1563])).

tff(c_4958,plain,(
    ! [A_145] :
      ( '#skF_3' = '#skF_4'
      | A_145 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1280,c_4941])).

tff(c_4990,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4958])).

tff(c_4984,plain,(
    ! [A_145] : A_145 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4958])).

tff(c_5424,plain,(
    ! [A_5974] : A_5974 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4990,c_4984])).

tff(c_5826,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5424,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:16:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.22  
% 5.51/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.51/2.22  
% 5.51/2.22  %Foreground sorts:
% 5.51/2.22  
% 5.51/2.22  
% 5.51/2.22  %Background operators:
% 5.51/2.22  
% 5.51/2.22  
% 5.51/2.22  %Foreground operators:
% 5.51/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.51/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.51/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.51/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.51/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.51/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.51/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.51/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.51/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.51/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.51/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.51/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.51/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.51/2.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.51/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.51/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.51/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.51/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.51/2.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.51/2.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.51/2.22  
% 5.51/2.23  tff(f_91, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 5.51/2.23  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 5.51/2.23  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.51/2.23  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.51/2.23  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.51/2.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.51/2.23  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.51/2.23  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.51/2.23  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.51/2.23  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.51/2.23  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.51/2.23  tff(f_70, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 5.51/2.23  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.51/2.23  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.51/2.23  tff(c_68, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.51/2.23  tff(c_48, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), k1_tarski(B_29))=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.51/2.23  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.51/2.23  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/2.23  tff(c_102, plain, (![B_79, A_80]: (r1_xboole_0(B_79, A_80) | ~r1_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.51/2.23  tff(c_105, plain, (![B_15, A_14]: (r1_xboole_0(B_15, k4_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_18, c_102])).
% 5.51/2.23  tff(c_120, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=k1_xboole_0 | ~r1_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.51/2.23  tff(c_131, plain, (![B_15, A_14]: (k3_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_120])).
% 5.51/2.23  tff(c_188, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.51/2.23  tff(c_197, plain, (![B_15, A_14]: (k4_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k5_xboole_0(B_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_131, c_188])).
% 5.51/2.23  tff(c_209, plain, (![B_15, A_14]: (k4_xboole_0(B_15, k4_xboole_0(A_14, B_15))=B_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_197])).
% 5.51/2.23  tff(c_424, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k3_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.51/2.23  tff(c_458, plain, (![B_15, A_14]: (k3_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_209, c_424])).
% 5.88/2.23  tff(c_469, plain, (![B_15]: (k4_xboole_0(B_15, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_458])).
% 5.88/2.23  tff(c_70, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.88/2.23  tff(c_111, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.88/2.23  tff(c_115, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_70, c_111])).
% 5.88/2.23  tff(c_200, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_188])).
% 5.88/2.23  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.23  tff(c_206, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_188])).
% 5.88/2.23  tff(c_330, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_206])).
% 5.88/2.23  tff(c_518, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_469, c_330])).
% 5.88/2.23  tff(c_633, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k4_xboole_0(B_121, A_120))=k2_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.88/2.23  tff(c_645, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_518, c_633])).
% 5.88/2.23  tff(c_657, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_645])).
% 5.88/2.23  tff(c_1002, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_657, c_48])).
% 5.88/2.23  tff(c_1186, plain, (![A_140, B_141, C_142]: (k2_xboole_0(k1_tarski(A_140), k2_tarski(B_141, C_142))=k1_enumset1(A_140, B_141, C_142))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.88/2.23  tff(c_1195, plain, (![A_140]: (k2_xboole_0(k1_tarski(A_140), k1_tarski('#skF_4'))=k1_enumset1(A_140, '#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_1186])).
% 5.88/2.23  tff(c_1258, plain, (![A_145]: (k1_enumset1(A_145, '#skF_4', '#skF_3')=k2_tarski(A_145, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1195])).
% 5.88/2.23  tff(c_24, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.88/2.23  tff(c_1280, plain, (![A_145]: (r2_hidden('#skF_3', k2_tarski(A_145, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1258, c_24])).
% 5.88/2.23  tff(c_56, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.88/2.23  tff(c_1563, plain, (![E_159, C_160, B_161, A_162]: (E_159=C_160 | E_159=B_161 | E_159=A_162 | ~r2_hidden(E_159, k1_enumset1(A_162, B_161, C_160)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.88/2.23  tff(c_4941, plain, (![E_287, B_288, A_289]: (E_287=B_288 | E_287=A_289 | E_287=A_289 | ~r2_hidden(E_287, k2_tarski(A_289, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1563])).
% 5.88/2.23  tff(c_4958, plain, (![A_145]: ('#skF_3'='#skF_4' | A_145='#skF_3')), inference(resolution, [status(thm)], [c_1280, c_4941])).
% 5.88/2.23  tff(c_4990, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_68, c_4958])).
% 5.88/2.23  tff(c_4984, plain, (![A_145]: (A_145='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_4958])).
% 5.88/2.23  tff(c_5424, plain, (![A_5974]: (A_5974='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4990, c_4984])).
% 5.88/2.23  tff(c_5826, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5424, c_68])).
% 5.88/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.23  
% 5.88/2.23  Inference rules
% 5.88/2.23  ----------------------
% 5.88/2.23  #Ref     : 0
% 5.88/2.23  #Sup     : 1558
% 5.88/2.23  #Fact    : 0
% 5.88/2.23  #Define  : 0
% 5.88/2.23  #Split   : 1
% 5.88/2.23  #Chain   : 0
% 5.88/2.23  #Close   : 0
% 5.88/2.23  
% 5.88/2.23  Ordering : KBO
% 5.88/2.23  
% 5.88/2.23  Simplification rules
% 5.88/2.23  ----------------------
% 5.88/2.23  #Subsume      : 253
% 5.88/2.23  #Demod        : 1125
% 5.88/2.23  #Tautology    : 941
% 5.88/2.23  #SimpNegUnit  : 12
% 5.88/2.23  #BackRed      : 7
% 5.88/2.23  
% 5.88/2.23  #Partial instantiations: 109
% 5.88/2.23  #Strategies tried      : 1
% 5.88/2.23  
% 5.88/2.23  Timing (in seconds)
% 5.88/2.23  ----------------------
% 5.88/2.24  Preprocessing        : 0.36
% 5.88/2.24  Parsing              : 0.18
% 5.88/2.24  CNF conversion       : 0.02
% 5.88/2.24  Main loop            : 1.09
% 5.88/2.24  Inferencing          : 0.38
% 5.88/2.24  Reduction            : 0.45
% 5.88/2.24  Demodulation         : 0.37
% 5.88/2.24  BG Simplification    : 0.04
% 5.88/2.24  Subsumption          : 0.16
% 5.88/2.24  Abstraction          : 0.06
% 5.88/2.24  MUC search           : 0.00
% 5.88/2.24  Cooper               : 0.00
% 5.88/2.24  Total                : 1.50
% 5.88/2.24  Index Insertion      : 0.00
% 5.88/2.24  Index Deletion       : 0.00
% 5.88/2.24  Index Matching       : 0.00
% 5.88/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
