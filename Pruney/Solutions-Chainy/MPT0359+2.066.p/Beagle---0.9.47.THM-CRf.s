%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:18 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 149 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 203 expanded)
%              Number of equality atoms :   43 ( 108 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_20,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_45,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_42])).

tff(c_103,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_129])).

tff(c_144,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_152,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_141])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_105,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_34])).

tff(c_169,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_105,c_169])).

tff(c_174,plain,(
    k3_subset_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_172])).

tff(c_36,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_104,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_110,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_104])).

tff(c_175,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_110])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_175])).

tff(c_179,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_179])).

tff(c_189,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_18,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_subset_1(A_25)) = k2_subset_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_subset_1(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28])).

tff(c_49,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_44])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k3_subset_1(A_21,B_22),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_188,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_250,plain,(
    ! [A_61,B_62] :
      ( k3_subset_1(A_61,k3_subset_1(A_61,B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_253,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_250])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( k1_subset_1(A_26) = B_27
      | ~ r1_tarski(B_27,k3_subset_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_283,plain,(
    ! [B_68,A_69] :
      ( k1_xboole_0 = B_68
      | ~ r1_tarski(B_68,k3_subset_1(A_69,B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_286,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_283])).

tff(c_295,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_286])).

tff(c_301,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_304,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_301])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_304])).

tff(c_309,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_312,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_253])).

tff(c_314,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_312])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.20/1.32  
% 2.20/1.32  %Foreground sorts:
% 2.20/1.32  
% 2.20/1.32  
% 2.20/1.32  %Background operators:
% 2.20/1.32  
% 2.20/1.32  
% 2.20/1.32  %Foreground operators:
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.20/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.32  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.20/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.20/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.32  
% 2.20/1.33  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.20/1.33  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.20/1.33  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.20/1.33  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.20/1.33  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.20/1.33  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.20/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.20/1.33  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.20/1.33  tff(f_43, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.20/1.33  tff(f_59, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.20/1.33  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.20/1.33  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.20/1.33  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.20/1.33  tff(c_20, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.33  tff(c_42, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.33  tff(c_45, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_42])).
% 2.20/1.33  tff(c_103, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_45])).
% 2.20/1.33  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.33  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.33  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.33  tff(c_129, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.33  tff(c_138, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_129])).
% 2.20/1.33  tff(c_144, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 2.20/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.33  tff(c_141, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_129])).
% 2.20/1.33  tff(c_152, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_141])).
% 2.20/1.33  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.33  tff(c_105, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_34])).
% 2.20/1.33  tff(c_169, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k3_subset_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.33  tff(c_172, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_105, c_169])).
% 2.20/1.33  tff(c_174, plain, (k3_subset_1('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_152, c_172])).
% 2.20/1.33  tff(c_36, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.33  tff(c_46, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_36])).
% 2.20/1.33  tff(c_104, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 2.20/1.33  tff(c_110, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_104])).
% 2.20/1.33  tff(c_175, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_110])).
% 2.20/1.33  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_175])).
% 2.20/1.33  tff(c_179, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 2.20/1.33  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_179])).
% 2.20/1.33  tff(c_189, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_45])).
% 2.20/1.33  tff(c_18, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.33  tff(c_28, plain, (![A_25]: (k3_subset_1(A_25, k1_subset_1(A_25))=k2_subset_1(A_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.20/1.33  tff(c_44, plain, (![A_25]: (k3_subset_1(A_25, k1_subset_1(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28])).
% 2.20/1.33  tff(c_49, plain, (![A_25]: (k3_subset_1(A_25, k1_xboole_0)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_44])).
% 2.20/1.33  tff(c_24, plain, (![A_21, B_22]: (m1_subset_1(k3_subset_1(A_21, B_22), k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.33  tff(c_188, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_45])).
% 2.20/1.33  tff(c_250, plain, (![A_61, B_62]: (k3_subset_1(A_61, k3_subset_1(A_61, B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.33  tff(c_253, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_250])).
% 2.20/1.33  tff(c_32, plain, (![A_26, B_27]: (k1_subset_1(A_26)=B_27 | ~r1_tarski(B_27, k3_subset_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.20/1.33  tff(c_283, plain, (![B_68, A_69]: (k1_xboole_0=B_68 | ~r1_tarski(B_68, k3_subset_1(A_69, B_68)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 2.20/1.33  tff(c_286, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_283])).
% 2.20/1.33  tff(c_295, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_286])).
% 2.20/1.33  tff(c_301, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_295])).
% 2.20/1.33  tff(c_304, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_301])).
% 2.20/1.33  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_304])).
% 2.20/1.33  tff(c_309, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_295])).
% 2.20/1.33  tff(c_312, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_253])).
% 2.20/1.33  tff(c_314, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_312])).
% 2.20/1.33  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_314])).
% 2.20/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.33  
% 2.20/1.33  Inference rules
% 2.20/1.33  ----------------------
% 2.20/1.33  #Ref     : 0
% 2.20/1.33  #Sup     : 59
% 2.20/1.33  #Fact    : 0
% 2.20/1.33  #Define  : 0
% 2.20/1.33  #Split   : 3
% 2.20/1.33  #Chain   : 0
% 2.20/1.33  #Close   : 0
% 2.20/1.33  
% 2.20/1.33  Ordering : KBO
% 2.20/1.33  
% 2.20/1.33  Simplification rules
% 2.20/1.33  ----------------------
% 2.20/1.33  #Subsume      : 1
% 2.20/1.33  #Demod        : 31
% 2.20/1.33  #Tautology    : 50
% 2.20/1.33  #SimpNegUnit  : 1
% 2.20/1.33  #BackRed      : 6
% 2.20/1.33  
% 2.20/1.33  #Partial instantiations: 0
% 2.20/1.33  #Strategies tried      : 1
% 2.20/1.33  
% 2.20/1.33  Timing (in seconds)
% 2.20/1.33  ----------------------
% 2.20/1.34  Preprocessing        : 0.31
% 2.20/1.34  Parsing              : 0.17
% 2.20/1.34  CNF conversion       : 0.02
% 2.20/1.34  Main loop            : 0.18
% 2.20/1.34  Inferencing          : 0.06
% 2.20/1.34  Reduction            : 0.06
% 2.20/1.34  Demodulation         : 0.04
% 2.20/1.34  BG Simplification    : 0.01
% 2.20/1.34  Subsumption          : 0.03
% 2.20/1.34  Abstraction          : 0.01
% 2.20/1.34  MUC search           : 0.00
% 2.20/1.34  Cooper               : 0.00
% 2.20/1.34  Total                : 0.53
% 2.20/1.34  Index Insertion      : 0.00
% 2.20/1.34  Index Deletion       : 0.00
% 2.20/1.34  Index Matching       : 0.00
% 2.20/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
