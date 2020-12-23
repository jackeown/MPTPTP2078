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
% DateTime   : Thu Dec  3 09:50:48 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :   66 ( 120 expanded)
%              Number of equality atoms :   46 (  91 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_293,plain,(
    ! [B_60,A_61] : k3_tarski(k2_tarski(B_60,A_61)) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_138])).

tff(c_40,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_320,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_40])).

tff(c_336,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_12])).

tff(c_440,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_447,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_336])).

tff(c_456,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = B_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_447])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_185,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_198,plain,(
    ! [A_55] : k3_xboole_0(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_185])).

tff(c_216,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_198])).

tff(c_473,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_482,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_473])).

tff(c_497,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_482])).

tff(c_196,plain,(
    ! [A_10] : k3_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_185])).

tff(c_488,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_473])).

tff(c_549,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_488])).

tff(c_498,plain,(
    ! [A_74,B_75] : k4_xboole_0(k2_xboole_0(A_74,B_75),B_75) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_521,plain,(
    ! [A_63] : k4_xboole_0(k1_xboole_0,A_63) = k4_xboole_0(A_63,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_498])).

tff(c_590,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_521])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_197,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_185])).

tff(c_485,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_473])).

tff(c_591,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_485])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_930,plain,(
    ! [A_98,B_99] :
      ( k3_xboole_0(k1_tarski(A_98),B_99) = k1_tarski(A_98)
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_38,c_185])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_939,plain,(
    ! [A_98,B_99] :
      ( k5_xboole_0(k1_tarski(A_98),k1_tarski(A_98)) = k4_xboole_0(k1_tarski(A_98),B_99)
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_10])).

tff(c_1091,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(k1_tarski(A_104),B_105) = k1_xboole_0
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_939])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1113,plain,(
    ! [B_105,A_104] :
      ( k2_xboole_0(B_105,k1_tarski(A_104)) = k2_xboole_0(B_105,k1_xboole_0)
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_18])).

tff(c_1328,plain,(
    ! [B_112,A_113] :
      ( k2_xboole_0(B_112,k1_tarski(A_113)) = B_112
      | ~ r2_hidden(A_113,B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1113])).

tff(c_299,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_40])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_319,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_42])).

tff(c_1363,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_319])).

tff(c_1411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.76/1.43  
% 2.76/1.43  %Foreground sorts:
% 2.76/1.43  
% 2.76/1.43  
% 2.76/1.43  %Background operators:
% 2.76/1.43  
% 2.76/1.43  
% 2.76/1.43  %Foreground operators:
% 2.76/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.43  
% 2.76/1.44  tff(f_72, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.76/1.44  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.76/1.44  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.76/1.44  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.76/1.44  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.76/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.76/1.44  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.44  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.76/1.44  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.76/1.44  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.76/1.44  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.44  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.76/1.44  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.76/1.44  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.44  tff(c_26, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.44  tff(c_138, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.44  tff(c_293, plain, (![B_60, A_61]: (k3_tarski(k2_tarski(B_60, A_61))=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_26, c_138])).
% 2.76/1.44  tff(c_40, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.44  tff(c_320, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_293, c_40])).
% 2.76/1.44  tff(c_336, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_320, c_12])).
% 2.76/1.44  tff(c_440, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.44  tff(c_447, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_440, c_336])).
% 2.76/1.44  tff(c_456, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=B_70)), inference(demodulation, [status(thm), theory('equality')], [c_336, c_447])).
% 2.76/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.44  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.76/1.44  tff(c_185, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.44  tff(c_198, plain, (![A_55]: (k3_xboole_0(k1_xboole_0, A_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_185])).
% 2.76/1.44  tff(c_216, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_198])).
% 2.76/1.44  tff(c_473, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.44  tff(c_482, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_216, c_473])).
% 2.76/1.44  tff(c_497, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_456, c_482])).
% 2.76/1.44  tff(c_196, plain, (![A_10]: (k3_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_185])).
% 2.76/1.44  tff(c_488, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_10))), inference(superposition, [status(thm), theory('equality')], [c_196, c_473])).
% 2.76/1.44  tff(c_549, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_497, c_488])).
% 2.76/1.44  tff(c_498, plain, (![A_74, B_75]: (k4_xboole_0(k2_xboole_0(A_74, B_75), B_75)=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.44  tff(c_521, plain, (![A_63]: (k4_xboole_0(k1_xboole_0, A_63)=k4_xboole_0(A_63, A_63))), inference(superposition, [status(thm), theory('equality')], [c_336, c_498])).
% 2.76/1.44  tff(c_590, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_549, c_521])).
% 2.76/1.44  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.44  tff(c_197, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_185])).
% 2.76/1.44  tff(c_485, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_197, c_473])).
% 2.76/1.44  tff(c_591, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_590, c_485])).
% 2.76/1.44  tff(c_38, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.76/1.44  tff(c_930, plain, (![A_98, B_99]: (k3_xboole_0(k1_tarski(A_98), B_99)=k1_tarski(A_98) | ~r2_hidden(A_98, B_99))), inference(resolution, [status(thm)], [c_38, c_185])).
% 2.76/1.44  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.44  tff(c_939, plain, (![A_98, B_99]: (k5_xboole_0(k1_tarski(A_98), k1_tarski(A_98))=k4_xboole_0(k1_tarski(A_98), B_99) | ~r2_hidden(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_930, c_10])).
% 2.76/1.44  tff(c_1091, plain, (![A_104, B_105]: (k4_xboole_0(k1_tarski(A_104), B_105)=k1_xboole_0 | ~r2_hidden(A_104, B_105))), inference(demodulation, [status(thm), theory('equality')], [c_591, c_939])).
% 2.76/1.44  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.44  tff(c_1113, plain, (![B_105, A_104]: (k2_xboole_0(B_105, k1_tarski(A_104))=k2_xboole_0(B_105, k1_xboole_0) | ~r2_hidden(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_18])).
% 2.76/1.44  tff(c_1328, plain, (![B_112, A_113]: (k2_xboole_0(B_112, k1_tarski(A_113))=B_112 | ~r2_hidden(A_113, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1113])).
% 2.76/1.44  tff(c_299, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_293, c_40])).
% 2.76/1.44  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.76/1.44  tff(c_319, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_42])).
% 2.76/1.44  tff(c_1363, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1328, c_319])).
% 2.76/1.44  tff(c_1411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1363])).
% 2.76/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.44  
% 2.76/1.44  Inference rules
% 2.76/1.44  ----------------------
% 2.76/1.44  #Ref     : 0
% 2.76/1.44  #Sup     : 317
% 2.76/1.44  #Fact    : 0
% 2.76/1.44  #Define  : 0
% 2.76/1.44  #Split   : 0
% 2.76/1.44  #Chain   : 0
% 2.76/1.44  #Close   : 0
% 2.76/1.44  
% 2.76/1.44  Ordering : KBO
% 2.76/1.44  
% 2.76/1.44  Simplification rules
% 2.76/1.44  ----------------------
% 2.76/1.44  #Subsume      : 12
% 2.76/1.44  #Demod        : 219
% 2.76/1.44  #Tautology    : 252
% 2.76/1.44  #SimpNegUnit  : 0
% 2.76/1.44  #BackRed      : 3
% 2.76/1.44  
% 2.76/1.44  #Partial instantiations: 0
% 2.76/1.44  #Strategies tried      : 1
% 2.76/1.44  
% 2.76/1.44  Timing (in seconds)
% 2.76/1.44  ----------------------
% 2.76/1.44  Preprocessing        : 0.31
% 2.76/1.44  Parsing              : 0.17
% 2.76/1.44  CNF conversion       : 0.02
% 2.76/1.44  Main loop            : 0.36
% 2.76/1.44  Inferencing          : 0.13
% 2.76/1.44  Reduction            : 0.14
% 2.76/1.44  Demodulation         : 0.11
% 2.76/1.44  BG Simplification    : 0.02
% 2.76/1.44  Subsumption          : 0.05
% 2.76/1.44  Abstraction          : 0.02
% 2.76/1.44  MUC search           : 0.00
% 2.76/1.44  Cooper               : 0.00
% 2.76/1.44  Total                : 0.71
% 2.76/1.44  Index Insertion      : 0.00
% 2.76/1.44  Index Deletion       : 0.00
% 2.76/1.44  Index Matching       : 0.00
% 2.76/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
