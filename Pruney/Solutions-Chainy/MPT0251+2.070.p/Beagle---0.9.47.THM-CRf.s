%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.82s
% Verified   : 
% Statistics : Number of formulae       :   64 (  73 expanded)
%              Number of leaves         :   34 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 (  86 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_76,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_64,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1247,plain,(
    ! [A_176,B_177,C_178] :
      ( ~ r2_hidden('#skF_2'(A_176,B_177,C_178),B_177)
      | r2_hidden('#skF_3'(A_176,B_177,C_178),C_178)
      | k4_xboole_0(A_176,B_177) = C_178 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1256,plain,(
    ! [A_179,C_180] :
      ( r2_hidden('#skF_3'(A_179,A_179,C_180),C_180)
      | k4_xboole_0(A_179,A_179) = C_180 ) ),
    inference(resolution,[status(thm)],[c_26,c_1247])).

tff(c_46,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [B_20] : r1_tarski(B_20,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_217,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_221,plain,(
    ! [B_20] : k3_xboole_0(B_20,B_20) = B_20 ),
    inference(resolution,[status(thm)],[c_36,c_217])).

tff(c_242,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,k3_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_246,plain,(
    ! [B_72,C_73] :
      ( ~ r1_xboole_0(B_72,B_72)
      | ~ r2_hidden(C_73,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_242])).

tff(c_250,plain,(
    ! [C_73] : ~ r2_hidden(C_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_1276,plain,(
    ! [A_179] : k4_xboole_0(A_179,A_179) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1256,c_250])).

tff(c_375,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_387,plain,(
    ! [B_20] : k5_xboole_0(B_20,B_20) = k4_xboole_0(B_20,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_375])).

tff(c_231,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_643,plain,(
    ! [A_115,B_116] :
      ( k3_xboole_0(k1_tarski(A_115),B_116) = k1_tarski(A_115)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_231,c_42])).

tff(c_38,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_659,plain,(
    ! [A_115,B_116] :
      ( k5_xboole_0(k1_tarski(A_115),k1_tarski(A_115)) = k4_xboole_0(k1_tarski(A_115),B_116)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_38])).

tff(c_679,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(k1_tarski(A_115),k1_tarski(A_115)) = k4_xboole_0(k1_tarski(A_115),B_116)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_659])).

tff(c_16705,plain,(
    ! [A_704,B_705] :
      ( k4_xboole_0(k1_tarski(A_704),B_705) = k1_xboole_0
      | ~ r2_hidden(A_704,B_705) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_679])).

tff(c_44,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_17040,plain,(
    ! [B_705,A_704] :
      ( k2_xboole_0(B_705,k1_tarski(A_704)) = k2_xboole_0(B_705,k1_xboole_0)
      | ~ r2_hidden(A_704,B_705) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16705,c_44])).

tff(c_17186,plain,(
    ! [B_706,A_707] :
      ( k2_xboole_0(B_706,k1_tarski(A_707)) = B_706
      | ~ r2_hidden(A_707,B_706) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17040])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_17222,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_17186,c_66])).

tff(c_17265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_17222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.49  
% 9.57/3.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.57/3.49  
% 9.57/3.49  %Foreground sorts:
% 9.57/3.49  
% 9.57/3.49  
% 9.57/3.49  %Background operators:
% 9.57/3.49  
% 9.57/3.49  
% 9.57/3.49  %Foreground operators:
% 9.57/3.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.57/3.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.57/3.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.57/3.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.57/3.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.57/3.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.57/3.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.57/3.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.57/3.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.57/3.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.57/3.49  tff('#skF_5', type, '#skF_5': $i).
% 9.57/3.49  tff('#skF_6', type, '#skF_6': $i).
% 9.57/3.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.57/3.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.57/3.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.57/3.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.57/3.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.57/3.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.57/3.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.57/3.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.57/3.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.57/3.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.57/3.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.57/3.49  
% 9.82/3.50  tff(f_95, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 9.82/3.50  tff(f_68, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.82/3.50  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.82/3.50  tff(f_76, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.82/3.50  tff(f_64, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.82/3.50  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.82/3.50  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.82/3.50  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.82/3.50  tff(f_88, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.82/3.50  tff(f_74, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.82/3.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.82/3.50  tff(c_64, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.82/3.50  tff(c_40, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.82/3.50  tff(c_26, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_2'(A_8, B_9, C_10), A_8) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.82/3.50  tff(c_1247, plain, (![A_176, B_177, C_178]: (~r2_hidden('#skF_2'(A_176, B_177, C_178), B_177) | r2_hidden('#skF_3'(A_176, B_177, C_178), C_178) | k4_xboole_0(A_176, B_177)=C_178)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.82/3.50  tff(c_1256, plain, (![A_179, C_180]: (r2_hidden('#skF_3'(A_179, A_179, C_180), C_180) | k4_xboole_0(A_179, A_179)=C_180)), inference(resolution, [status(thm)], [c_26, c_1247])).
% 9.82/3.50  tff(c_46, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.82/3.50  tff(c_36, plain, (![B_20]: (r1_tarski(B_20, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.82/3.50  tff(c_217, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.82/3.50  tff(c_221, plain, (![B_20]: (k3_xboole_0(B_20, B_20)=B_20)), inference(resolution, [status(thm)], [c_36, c_217])).
% 9.82/3.50  tff(c_242, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.82/3.50  tff(c_246, plain, (![B_72, C_73]: (~r1_xboole_0(B_72, B_72) | ~r2_hidden(C_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_221, c_242])).
% 9.82/3.50  tff(c_250, plain, (![C_73]: (~r2_hidden(C_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_246])).
% 9.82/3.50  tff(c_1276, plain, (![A_179]: (k4_xboole_0(A_179, A_179)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1256, c_250])).
% 9.82/3.50  tff(c_375, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.82/3.50  tff(c_387, plain, (![B_20]: (k5_xboole_0(B_20, B_20)=k4_xboole_0(B_20, B_20))), inference(superposition, [status(thm), theory('equality')], [c_221, c_375])).
% 9.82/3.50  tff(c_231, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.82/3.50  tff(c_42, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.82/3.50  tff(c_643, plain, (![A_115, B_116]: (k3_xboole_0(k1_tarski(A_115), B_116)=k1_tarski(A_115) | ~r2_hidden(A_115, B_116))), inference(resolution, [status(thm)], [c_231, c_42])).
% 9.82/3.50  tff(c_38, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.82/3.50  tff(c_659, plain, (![A_115, B_116]: (k5_xboole_0(k1_tarski(A_115), k1_tarski(A_115))=k4_xboole_0(k1_tarski(A_115), B_116) | ~r2_hidden(A_115, B_116))), inference(superposition, [status(thm), theory('equality')], [c_643, c_38])).
% 9.82/3.50  tff(c_679, plain, (![A_115, B_116]: (k4_xboole_0(k1_tarski(A_115), k1_tarski(A_115))=k4_xboole_0(k1_tarski(A_115), B_116) | ~r2_hidden(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_659])).
% 9.82/3.50  tff(c_16705, plain, (![A_704, B_705]: (k4_xboole_0(k1_tarski(A_704), B_705)=k1_xboole_0 | ~r2_hidden(A_704, B_705))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_679])).
% 9.82/3.50  tff(c_44, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.82/3.50  tff(c_17040, plain, (![B_705, A_704]: (k2_xboole_0(B_705, k1_tarski(A_704))=k2_xboole_0(B_705, k1_xboole_0) | ~r2_hidden(A_704, B_705))), inference(superposition, [status(thm), theory('equality')], [c_16705, c_44])).
% 9.82/3.50  tff(c_17186, plain, (![B_706, A_707]: (k2_xboole_0(B_706, k1_tarski(A_707))=B_706 | ~r2_hidden(A_707, B_706))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_17040])).
% 9.82/3.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.82/3.50  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.82/3.50  tff(c_66, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 9.82/3.50  tff(c_17222, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_17186, c_66])).
% 9.82/3.50  tff(c_17265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_17222])).
% 9.82/3.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.82/3.50  
% 9.82/3.50  Inference rules
% 9.82/3.50  ----------------------
% 9.82/3.50  #Ref     : 0
% 9.82/3.50  #Sup     : 4456
% 9.82/3.50  #Fact    : 0
% 9.82/3.50  #Define  : 0
% 9.82/3.50  #Split   : 4
% 9.82/3.50  #Chain   : 0
% 9.82/3.50  #Close   : 0
% 9.82/3.50  
% 9.82/3.50  Ordering : KBO
% 9.82/3.50  
% 9.82/3.50  Simplification rules
% 9.82/3.50  ----------------------
% 9.82/3.50  #Subsume      : 2248
% 9.82/3.50  #Demod        : 2024
% 9.82/3.50  #Tautology    : 940
% 9.82/3.50  #SimpNegUnit  : 92
% 9.82/3.50  #BackRed      : 5
% 9.82/3.50  
% 9.82/3.50  #Partial instantiations: 0
% 9.82/3.50  #Strategies tried      : 1
% 9.82/3.50  
% 9.82/3.50  Timing (in seconds)
% 9.82/3.50  ----------------------
% 9.82/3.51  Preprocessing        : 0.35
% 9.82/3.51  Parsing              : 0.18
% 9.82/3.51  CNF conversion       : 0.03
% 9.82/3.51  Main loop            : 2.34
% 9.82/3.51  Inferencing          : 0.63
% 9.82/3.51  Reduction            : 0.73
% 9.82/3.51  Demodulation         : 0.53
% 9.82/3.51  BG Simplification    : 0.06
% 9.82/3.51  Subsumption          : 0.79
% 9.82/3.51  Abstraction          : 0.10
% 9.82/3.51  MUC search           : 0.00
% 9.82/3.51  Cooper               : 0.00
% 9.82/3.51  Total                : 2.72
% 9.82/3.51  Index Insertion      : 0.00
% 9.82/3.51  Index Deletion       : 0.00
% 9.82/3.51  Index Matching       : 0.00
% 9.82/3.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
