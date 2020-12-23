%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:47 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 136 expanded)
%              Number of leaves         :   38 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :   94 ( 177 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_68,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_42])).

tff(c_48,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_177,plain,(
    ! [A_59] : r1_tarski(k1_xboole_0,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_48])).

tff(c_372,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_394,plain,(
    ! [A_59] : k3_xboole_0(k1_xboole_0,A_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_372])).

tff(c_632,plain,(
    ! [D_105,B_106,A_107] :
      ( r2_hidden(D_105,B_106)
      | ~ r2_hidden(D_105,k3_xboole_0(A_107,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_856,plain,(
    ! [D_126,A_127] :
      ( r2_hidden(D_126,A_127)
      | ~ r2_hidden(D_126,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_632])).

tff(c_868,plain,(
    ! [A_127] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_127)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_856])).

tff(c_911,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_614,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_4'(A_100,B_101),A_100)
      | r1_xboole_0(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_621,plain,(
    ! [A_100,B_101] :
      ( ~ v1_xboole_0(A_100)
      | r1_xboole_0(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_614,c_6])).

tff(c_134,plain,(
    ! [A_58] : k2_xboole_0(k1_xboole_0,A_58) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_42])).

tff(c_913,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(k2_xboole_0(A_132,B_133),B_133) = A_132
      | ~ r1_xboole_0(A_132,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1006,plain,(
    ! [A_139] :
      ( k4_xboole_0(A_139,A_139) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_913])).

tff(c_1012,plain,(
    ! [B_101] :
      ( k4_xboole_0(B_101,B_101) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_621,c_1006])).

tff(c_1016,plain,(
    ! [B_101] : k4_xboole_0(B_101,B_101) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_1012])).

tff(c_38,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_396,plain,(
    ! [B_21] : k3_xboole_0(B_21,B_21) = B_21 ),
    inference(resolution,[status(thm)],[c_38,c_372])).

tff(c_707,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k3_xboole_0(A_114,B_115)) = k4_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_728,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k4_xboole_0(B_21,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_707])).

tff(c_1018,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_728])).

tff(c_62,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2285,plain,(
    ! [A_227,B_228] :
      ( k3_xboole_0(k1_tarski(A_227),B_228) = k1_tarski(A_227)
      | ~ r2_hidden(A_227,B_228) ) ),
    inference(resolution,[status(thm)],[c_62,c_372])).

tff(c_40,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2294,plain,(
    ! [A_227,B_228] :
      ( k5_xboole_0(k1_tarski(A_227),k1_tarski(A_227)) = k4_xboole_0(k1_tarski(A_227),B_228)
      | ~ r2_hidden(A_227,B_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2285,c_40])).

tff(c_2562,plain,(
    ! [A_241,B_242] :
      ( k4_xboole_0(k1_tarski(A_241),B_242) = k1_xboole_0
      | ~ r2_hidden(A_241,B_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_2294])).

tff(c_46,plain,(
    ! [A_27,B_28] : k2_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2593,plain,(
    ! [B_242,A_241] :
      ( k2_xboole_0(B_242,k1_tarski(A_241)) = k2_xboole_0(B_242,k1_xboole_0)
      | ~ r2_hidden(A_241,B_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2562,c_46])).

tff(c_3408,plain,(
    ! [B_283,A_284] :
      ( k2_xboole_0(B_283,k1_tarski(A_284)) = B_283
      | ~ r2_hidden(A_284,B_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2593])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_66])).

tff(c_3591,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3408,c_70])).

tff(c_3638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3591])).

tff(c_3641,plain,(
    ! [A_285] : r2_hidden('#skF_1'(k1_xboole_0),A_285) ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_3675,plain,(
    ! [A_285] : ~ v1_xboole_0(A_285) ),
    inference(resolution,[status(thm)],[c_3641,c_6])).

tff(c_105,plain,(
    ! [B_55,A_56] :
      ( ~ r2_hidden(B_55,A_56)
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_110,plain,(
    ! [A_5] :
      ( ~ r2_hidden(A_5,'#skF_1'(A_5))
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_3673,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3641,c_110])).

tff(c_3720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3675,c_3673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.78  
% 4.42/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.42/1.78  
% 4.42/1.78  %Foreground sorts:
% 4.42/1.78  
% 4.42/1.78  
% 4.42/1.78  %Background operators:
% 4.42/1.78  
% 4.42/1.78  
% 4.42/1.78  %Foreground operators:
% 4.42/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.42/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.42/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.42/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.42/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.42/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.42/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.42/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.42/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.42/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.42/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.42/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.42/1.78  
% 4.42/1.80  tff(f_106, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.42/1.80  tff(f_75, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.42/1.80  tff(f_38, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.42/1.80  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.42/1.80  tff(f_83, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.42/1.80  tff(f_79, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.42/1.80  tff(f_47, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.42/1.80  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.42/1.80  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.42/1.80  tff(f_71, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.42/1.80  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.42/1.80  tff(f_99, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.42/1.80  tff(f_81, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.42/1.80  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 4.42/1.80  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.42/1.80  tff(c_42, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.42/1.80  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.42/1.80  tff(c_112, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.42/1.80  tff(c_165, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_112, c_42])).
% 4.42/1.80  tff(c_48, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.42/1.80  tff(c_177, plain, (![A_59]: (r1_tarski(k1_xboole_0, A_59))), inference(superposition, [status(thm), theory('equality')], [c_165, c_48])).
% 4.42/1.80  tff(c_372, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.42/1.80  tff(c_394, plain, (![A_59]: (k3_xboole_0(k1_xboole_0, A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_372])).
% 4.42/1.80  tff(c_632, plain, (![D_105, B_106, A_107]: (r2_hidden(D_105, B_106) | ~r2_hidden(D_105, k3_xboole_0(A_107, B_106)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.42/1.80  tff(c_856, plain, (![D_126, A_127]: (r2_hidden(D_126, A_127) | ~r2_hidden(D_126, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_394, c_632])).
% 4.42/1.80  tff(c_868, plain, (![A_127]: (r2_hidden('#skF_1'(k1_xboole_0), A_127) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_856])).
% 4.42/1.80  tff(c_911, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_868])).
% 4.42/1.80  tff(c_614, plain, (![A_100, B_101]: (r2_hidden('#skF_4'(A_100, B_101), A_100) | r1_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.42/1.80  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.42/1.80  tff(c_621, plain, (![A_100, B_101]: (~v1_xboole_0(A_100) | r1_xboole_0(A_100, B_101))), inference(resolution, [status(thm)], [c_614, c_6])).
% 4.42/1.80  tff(c_134, plain, (![A_58]: (k2_xboole_0(k1_xboole_0, A_58)=A_58)), inference(superposition, [status(thm), theory('equality')], [c_112, c_42])).
% 4.42/1.80  tff(c_913, plain, (![A_132, B_133]: (k4_xboole_0(k2_xboole_0(A_132, B_133), B_133)=A_132 | ~r1_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.42/1.80  tff(c_1006, plain, (![A_139]: (k4_xboole_0(A_139, A_139)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_139))), inference(superposition, [status(thm), theory('equality')], [c_134, c_913])).
% 4.42/1.80  tff(c_1012, plain, (![B_101]: (k4_xboole_0(B_101, B_101)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_621, c_1006])).
% 4.42/1.80  tff(c_1016, plain, (![B_101]: (k4_xboole_0(B_101, B_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_911, c_1012])).
% 4.42/1.80  tff(c_38, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.42/1.80  tff(c_396, plain, (![B_21]: (k3_xboole_0(B_21, B_21)=B_21)), inference(resolution, [status(thm)], [c_38, c_372])).
% 4.42/1.80  tff(c_707, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k3_xboole_0(A_114, B_115))=k4_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.42/1.80  tff(c_728, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k4_xboole_0(B_21, B_21))), inference(superposition, [status(thm), theory('equality')], [c_396, c_707])).
% 4.42/1.80  tff(c_1018, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_728])).
% 4.42/1.80  tff(c_62, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.42/1.80  tff(c_2285, plain, (![A_227, B_228]: (k3_xboole_0(k1_tarski(A_227), B_228)=k1_tarski(A_227) | ~r2_hidden(A_227, B_228))), inference(resolution, [status(thm)], [c_62, c_372])).
% 4.42/1.80  tff(c_40, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.42/1.80  tff(c_2294, plain, (![A_227, B_228]: (k5_xboole_0(k1_tarski(A_227), k1_tarski(A_227))=k4_xboole_0(k1_tarski(A_227), B_228) | ~r2_hidden(A_227, B_228))), inference(superposition, [status(thm), theory('equality')], [c_2285, c_40])).
% 4.42/1.80  tff(c_2562, plain, (![A_241, B_242]: (k4_xboole_0(k1_tarski(A_241), B_242)=k1_xboole_0 | ~r2_hidden(A_241, B_242))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_2294])).
% 4.42/1.80  tff(c_46, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.42/1.80  tff(c_2593, plain, (![B_242, A_241]: (k2_xboole_0(B_242, k1_tarski(A_241))=k2_xboole_0(B_242, k1_xboole_0) | ~r2_hidden(A_241, B_242))), inference(superposition, [status(thm), theory('equality')], [c_2562, c_46])).
% 4.42/1.80  tff(c_3408, plain, (![B_283, A_284]: (k2_xboole_0(B_283, k1_tarski(A_284))=B_283 | ~r2_hidden(A_284, B_283))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2593])).
% 4.42/1.80  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.42/1.80  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.42/1.80  tff(c_70, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_66])).
% 4.42/1.80  tff(c_3591, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3408, c_70])).
% 4.42/1.80  tff(c_3638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_3591])).
% 4.42/1.80  tff(c_3641, plain, (![A_285]: (r2_hidden('#skF_1'(k1_xboole_0), A_285))), inference(splitRight, [status(thm)], [c_868])).
% 4.42/1.80  tff(c_3675, plain, (![A_285]: (~v1_xboole_0(A_285))), inference(resolution, [status(thm)], [c_3641, c_6])).
% 4.42/1.80  tff(c_105, plain, (![B_55, A_56]: (~r2_hidden(B_55, A_56) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.42/1.80  tff(c_110, plain, (![A_5]: (~r2_hidden(A_5, '#skF_1'(A_5)) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_8, c_105])).
% 4.42/1.80  tff(c_3673, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_3641, c_110])).
% 4.42/1.80  tff(c_3720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3675, c_3673])).
% 4.42/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.80  
% 4.42/1.80  Inference rules
% 4.42/1.80  ----------------------
% 4.42/1.80  #Ref     : 0
% 4.42/1.80  #Sup     : 901
% 4.42/1.80  #Fact    : 0
% 4.42/1.80  #Define  : 0
% 4.42/1.80  #Split   : 2
% 4.42/1.80  #Chain   : 0
% 4.42/1.80  #Close   : 0
% 4.42/1.80  
% 4.42/1.80  Ordering : KBO
% 4.42/1.80  
% 4.42/1.80  Simplification rules
% 4.42/1.80  ----------------------
% 4.42/1.80  #Subsume      : 328
% 4.42/1.80  #Demod        : 282
% 4.42/1.80  #Tautology    : 323
% 4.42/1.80  #SimpNegUnit  : 12
% 4.42/1.80  #BackRed      : 11
% 4.42/1.80  
% 4.42/1.80  #Partial instantiations: 0
% 4.42/1.80  #Strategies tried      : 1
% 4.42/1.80  
% 4.42/1.80  Timing (in seconds)
% 4.42/1.80  ----------------------
% 4.42/1.80  Preprocessing        : 0.32
% 4.42/1.80  Parsing              : 0.17
% 4.42/1.80  CNF conversion       : 0.02
% 4.42/1.80  Main loop            : 0.71
% 4.42/1.80  Inferencing          : 0.23
% 4.42/1.80  Reduction            : 0.25
% 4.42/1.80  Demodulation         : 0.19
% 4.42/1.80  BG Simplification    : 0.03
% 4.42/1.80  Subsumption          : 0.15
% 4.42/1.80  Abstraction          : 0.03
% 4.42/1.80  MUC search           : 0.00
% 4.42/1.80  Cooper               : 0.00
% 4.42/1.80  Total                : 1.06
% 4.42/1.80  Index Insertion      : 0.00
% 4.42/1.80  Index Deletion       : 0.00
% 4.42/1.80  Index Matching       : 0.00
% 4.42/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
