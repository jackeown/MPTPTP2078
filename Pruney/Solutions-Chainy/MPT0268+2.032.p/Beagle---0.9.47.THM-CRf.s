%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:38 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   74 (  87 expanded)
%              Number of leaves         :   36 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  92 expanded)
%              Number of equality atoms :   37 (  47 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_70,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [A_50] : k3_tarski(k1_tarski(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_149,plain,(
    ! [A_71,B_72] : k3_tarski(k2_tarski(A_71,B_72)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_158,plain,(
    ! [A_18] : k3_tarski(k1_tarski(A_18)) = k2_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_162,plain,(
    ! [A_73] : k2_xboole_0(A_73,A_73) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_158])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_168,plain,(
    ! [A_73] : k4_xboole_0(A_73,A_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_12])).

tff(c_189,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(k1_tarski(A_76),B_77)
      | r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1892,plain,(
    ! [A_167,B_168] :
      ( k4_xboole_0(k1_tarski(A_167),B_168) = k1_tarski(A_167)
      | r2_hidden(A_167,B_168) ) ),
    inference(resolution,[status(thm)],[c_189,c_18])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1929,plain,(
    ! [A_167,B_168] :
      ( k4_xboole_0(k1_tarski(A_167),k1_tarski(A_167)) = k3_xboole_0(k1_tarski(A_167),B_168)
      | r2_hidden(A_167,B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_14])).

tff(c_2268,plain,(
    ! [A_176,B_177] :
      ( k3_xboole_0(k1_tarski(A_176),B_177) = k1_xboole_0
      | r2_hidden(A_176,B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1929])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_391,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_406,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_391])).

tff(c_2326,plain,(
    ! [B_177,A_176] :
      ( k4_xboole_0(B_177,k1_tarski(A_176)) = k5_xboole_0(B_177,k1_xboole_0)
      | r2_hidden(A_176,B_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2268,c_406])).

tff(c_2405,plain,(
    ! [B_178,A_179] :
      ( k4_xboole_0(B_178,k1_tarski(A_179)) = B_178
      | r2_hidden(A_179,B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2326])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_127,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2460,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2405,c_127])).

tff(c_2506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2460])).

tff(c_2507,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2508,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2641,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2508,c_52])).

tff(c_44,plain,(
    ! [C_53,B_52] : ~ r2_hidden(C_53,k4_xboole_0(B_52,k1_tarski(C_53))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2645,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2641,c_44])).

tff(c_2653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2507,c_2645])).

tff(c_2654,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2655,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2847,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_54])).

tff(c_2851,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2847,c_44])).

tff(c_2859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_2851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/2.23  
% 4.66/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/2.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.66/2.24  
% 4.66/2.24  %Foreground sorts:
% 4.66/2.24  
% 4.66/2.24  
% 4.66/2.24  %Background operators:
% 4.66/2.24  
% 4.66/2.24  
% 4.66/2.24  %Foreground operators:
% 4.66/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.66/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.66/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.66/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/2.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.66/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.66/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/2.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.66/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.66/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.66/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.66/2.24  tff('#skF_2', type, '#skF_2': $i).
% 4.66/2.24  tff('#skF_3', type, '#skF_3': $i).
% 4.66/2.24  tff('#skF_1', type, '#skF_1': $i).
% 4.66/2.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.66/2.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.66/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.66/2.24  tff('#skF_4', type, '#skF_4': $i).
% 4.66/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.66/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.66/2.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.66/2.24  
% 4.66/2.26  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.66/2.26  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.66/2.26  tff(f_70, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 4.66/2.26  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.66/2.26  tff(f_68, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.66/2.26  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.66/2.26  tff(f_66, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.66/2.26  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.66/2.26  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.66/2.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.66/2.26  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.66/2.26  tff(f_77, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.66/2.26  tff(c_50, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.66/2.26  tff(c_92, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.66/2.26  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/2.26  tff(c_40, plain, (![A_50]: (k3_tarski(k1_tarski(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.66/2.26  tff(c_22, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.66/2.26  tff(c_149, plain, (![A_71, B_72]: (k3_tarski(k2_tarski(A_71, B_72))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.66/2.26  tff(c_158, plain, (![A_18]: (k3_tarski(k1_tarski(A_18))=k2_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_149])).
% 4.66/2.26  tff(c_162, plain, (![A_73]: (k2_xboole_0(A_73, A_73)=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_158])).
% 4.66/2.26  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/2.26  tff(c_168, plain, (![A_73]: (k4_xboole_0(A_73, A_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_162, c_12])).
% 4.66/2.26  tff(c_189, plain, (![A_76, B_77]: (r1_xboole_0(k1_tarski(A_76), B_77) | r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.66/2.26  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.66/2.26  tff(c_1892, plain, (![A_167, B_168]: (k4_xboole_0(k1_tarski(A_167), B_168)=k1_tarski(A_167) | r2_hidden(A_167, B_168))), inference(resolution, [status(thm)], [c_189, c_18])).
% 4.66/2.26  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.66/2.26  tff(c_1929, plain, (![A_167, B_168]: (k4_xboole_0(k1_tarski(A_167), k1_tarski(A_167))=k3_xboole_0(k1_tarski(A_167), B_168) | r2_hidden(A_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_1892, c_14])).
% 4.66/2.26  tff(c_2268, plain, (![A_176, B_177]: (k3_xboole_0(k1_tarski(A_176), B_177)=k1_xboole_0 | r2_hidden(A_176, B_177))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_1929])).
% 4.66/2.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/2.26  tff(c_391, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/2.26  tff(c_406, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_391])).
% 4.66/2.26  tff(c_2326, plain, (![B_177, A_176]: (k4_xboole_0(B_177, k1_tarski(A_176))=k5_xboole_0(B_177, k1_xboole_0) | r2_hidden(A_176, B_177))), inference(superposition, [status(thm), theory('equality')], [c_2268, c_406])).
% 4.66/2.26  tff(c_2405, plain, (![B_178, A_179]: (k4_xboole_0(B_178, k1_tarski(A_179))=B_178 | r2_hidden(A_179, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2326])).
% 4.66/2.26  tff(c_48, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.66/2.26  tff(c_127, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_48])).
% 4.66/2.26  tff(c_2460, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2405, c_127])).
% 4.66/2.26  tff(c_2506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_2460])).
% 4.66/2.26  tff(c_2507, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 4.66/2.26  tff(c_2508, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 4.66/2.26  tff(c_52, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.66/2.26  tff(c_2641, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2508, c_52])).
% 4.66/2.26  tff(c_44, plain, (![C_53, B_52]: (~r2_hidden(C_53, k4_xboole_0(B_52, k1_tarski(C_53))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.66/2.26  tff(c_2645, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2641, c_44])).
% 4.66/2.26  tff(c_2653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2507, c_2645])).
% 4.66/2.26  tff(c_2654, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 4.66/2.26  tff(c_2655, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.66/2.26  tff(c_54, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.66/2.26  tff(c_2847, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_54])).
% 4.66/2.26  tff(c_2851, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2847, c_44])).
% 4.66/2.26  tff(c_2859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2654, c_2851])).
% 4.66/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/2.26  
% 4.66/2.26  Inference rules
% 4.66/2.26  ----------------------
% 4.66/2.26  #Ref     : 0
% 4.66/2.26  #Sup     : 678
% 4.66/2.26  #Fact    : 0
% 4.66/2.26  #Define  : 0
% 4.66/2.26  #Split   : 2
% 4.66/2.26  #Chain   : 0
% 4.66/2.26  #Close   : 0
% 4.66/2.26  
% 4.66/2.26  Ordering : KBO
% 4.66/2.26  
% 4.66/2.26  Simplification rules
% 4.66/2.26  ----------------------
% 4.66/2.26  #Subsume      : 48
% 4.66/2.26  #Demod        : 540
% 4.66/2.26  #Tautology    : 478
% 4.66/2.26  #SimpNegUnit  : 12
% 4.66/2.26  #BackRed      : 0
% 4.66/2.26  
% 4.66/2.26  #Partial instantiations: 0
% 4.66/2.26  #Strategies tried      : 1
% 4.66/2.26  
% 4.66/2.26  Timing (in seconds)
% 4.66/2.26  ----------------------
% 4.66/2.26  Preprocessing        : 0.50
% 4.66/2.26  Parsing              : 0.26
% 4.66/2.26  CNF conversion       : 0.03
% 4.66/2.26  Main loop            : 0.85
% 4.66/2.26  Inferencing          : 0.29
% 4.66/2.26  Reduction            : 0.35
% 4.66/2.26  Demodulation         : 0.28
% 4.66/2.26  BG Simplification    : 0.04
% 4.66/2.26  Subsumption          : 0.11
% 4.66/2.26  Abstraction          : 0.05
% 4.66/2.26  MUC search           : 0.00
% 4.66/2.26  Cooper               : 0.00
% 4.66/2.26  Total                : 1.40
% 4.66/2.26  Index Insertion      : 0.00
% 4.66/2.27  Index Deletion       : 0.00
% 4.66/2.27  Index Matching       : 0.00
% 4.66/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
