%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:10 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 121 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   76 ( 220 expanded)
%              Number of equality atoms :   39 (  98 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9850,plain,(
    ! [A_5666,B_5667,C_5668] :
      ( ~ r2_hidden('#skF_1'(A_5666,B_5667,C_5668),B_5667)
      | r2_hidden('#skF_2'(A_5666,B_5667,C_5668),C_5668)
      | k4_xboole_0(A_5666,B_5667) = C_5668 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9853,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_9850])).

tff(c_9873,plain,(
    ! [A_5691,C_5692] :
      ( r2_hidden('#skF_2'(A_5691,A_5691,C_5692),C_5692)
      | k1_xboole_0 = C_5692 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_9853])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10844,plain,(
    ! [A_6214,A_6215,B_6216] :
      ( r2_hidden('#skF_2'(A_6214,A_6214,k4_xboole_0(A_6215,B_6216)),A_6215)
      | k4_xboole_0(A_6215,B_6216) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9873,c_6])).

tff(c_36,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12131,plain,(
    ! [A_6555,A_6556,B_6557] :
      ( '#skF_2'(A_6555,A_6555,k4_xboole_0(k1_tarski(A_6556),B_6557)) = A_6556
      | k4_xboole_0(k1_tarski(A_6556),B_6557) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10844,c_36])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9918,plain,(
    ! [A_5691,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_5691,A_5691,k4_xboole_0(A_1,B_2)),B_2)
      | k4_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9873,c_4])).

tff(c_12144,plain,(
    ! [A_6556,B_6557] :
      ( ~ r2_hidden(A_6556,B_6557)
      | k4_xboole_0(k1_tarski(A_6556),B_6557) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_6556),B_6557) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12131,c_9918])).

tff(c_16346,plain,(
    ! [A_7450,B_7451] :
      ( ~ r2_hidden(A_7450,B_7451)
      | k4_xboole_0(k1_tarski(A_7450),B_7451) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12144])).

tff(c_54,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16520,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16346,c_54])).

tff(c_32,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_145,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_166,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_145])).

tff(c_171,plain,(
    ! [A_48] : k3_xboole_0(A_48,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_166])).

tff(c_30,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_176,plain,(
    ! [A_48] : k5_xboole_0(A_48,k1_xboole_0) = k4_xboole_0(A_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_30])).

tff(c_180,plain,(
    ! [A_48] : k5_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_176])).

tff(c_38,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17216,plain,(
    ! [A_7641,B_7642] :
      ( k3_xboole_0(k1_tarski(A_7641),B_7642) = k1_xboole_0
      | ~ r2_hidden(A_7641,k4_xboole_0(k1_tarski(A_7641),B_7642)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16346,c_34])).

tff(c_17259,plain,(
    ! [D_6,B_2] :
      ( k3_xboole_0(k1_tarski(D_6),B_2) = k1_xboole_0
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k1_tarski(D_6)) ) ),
    inference(resolution,[status(thm)],[c_2,c_17216])).

tff(c_17283,plain,(
    ! [D_7665,B_7666] :
      ( k3_xboole_0(k1_tarski(D_7665),B_7666) = k1_xboole_0
      | r2_hidden(D_7665,B_7666) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_17259])).

tff(c_17378,plain,(
    ! [D_7665,B_7666] :
      ( k5_xboole_0(k1_tarski(D_7665),k1_xboole_0) = k4_xboole_0(k1_tarski(D_7665),B_7666)
      | r2_hidden(D_7665,B_7666) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17283,c_30])).

tff(c_17482,plain,(
    ! [D_7689,B_7690] :
      ( k4_xboole_0(k1_tarski(D_7689),B_7690) = k1_tarski(D_7689)
      | r2_hidden(D_7689,B_7690) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_17378])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_17579,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_17482,c_52])).

tff(c_17682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16520,c_17579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 10:43:16 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.70  
% 7.68/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.70  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.75/2.70  
% 7.75/2.70  %Foreground sorts:
% 7.75/2.70  
% 7.75/2.70  
% 7.75/2.70  %Background operators:
% 7.75/2.70  
% 7.75/2.70  
% 7.75/2.70  %Foreground operators:
% 7.75/2.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.75/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.75/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.75/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.75/2.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.75/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.75/2.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.75/2.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.75/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.75/2.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.75/2.70  tff('#skF_5', type, '#skF_5': $i).
% 7.75/2.70  tff('#skF_6', type, '#skF_6': $i).
% 7.75/2.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.75/2.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.75/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.75/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.75/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.75/2.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.75/2.70  
% 7.75/2.71  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.75/2.71  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.75/2.71  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.75/2.71  tff(f_58, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.75/2.71  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 7.75/2.71  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.75/2.71  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.75/2.71  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.75/2.71  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.75/2.71  tff(c_92, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.75/2.71  tff(c_100, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_92])).
% 7.75/2.71  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.75/2.71  tff(c_9850, plain, (![A_5666, B_5667, C_5668]: (~r2_hidden('#skF_1'(A_5666, B_5667, C_5668), B_5667) | r2_hidden('#skF_2'(A_5666, B_5667, C_5668), C_5668) | k4_xboole_0(A_5666, B_5667)=C_5668)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.75/2.71  tff(c_9853, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_9850])).
% 7.75/2.71  tff(c_9873, plain, (![A_5691, C_5692]: (r2_hidden('#skF_2'(A_5691, A_5691, C_5692), C_5692) | k1_xboole_0=C_5692)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_9853])).
% 7.75/2.71  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.75/2.71  tff(c_10844, plain, (![A_6214, A_6215, B_6216]: (r2_hidden('#skF_2'(A_6214, A_6214, k4_xboole_0(A_6215, B_6216)), A_6215) | k4_xboole_0(A_6215, B_6216)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9873, c_6])).
% 7.75/2.71  tff(c_36, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.75/2.71  tff(c_12131, plain, (![A_6555, A_6556, B_6557]: ('#skF_2'(A_6555, A_6555, k4_xboole_0(k1_tarski(A_6556), B_6557))=A_6556 | k4_xboole_0(k1_tarski(A_6556), B_6557)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10844, c_36])).
% 7.75/2.71  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.75/2.71  tff(c_9918, plain, (![A_5691, A_1, B_2]: (~r2_hidden('#skF_2'(A_5691, A_5691, k4_xboole_0(A_1, B_2)), B_2) | k4_xboole_0(A_1, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9873, c_4])).
% 7.75/2.71  tff(c_12144, plain, (![A_6556, B_6557]: (~r2_hidden(A_6556, B_6557) | k4_xboole_0(k1_tarski(A_6556), B_6557)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_6556), B_6557)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12131, c_9918])).
% 7.75/2.71  tff(c_16346, plain, (![A_7450, B_7451]: (~r2_hidden(A_7450, B_7451) | k4_xboole_0(k1_tarski(A_7450), B_7451)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_12144])).
% 7.75/2.71  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.75/2.71  tff(c_16520, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_16346, c_54])).
% 7.75/2.71  tff(c_32, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.75/2.71  tff(c_145, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.75/2.71  tff(c_166, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_145])).
% 7.75/2.71  tff(c_171, plain, (![A_48]: (k3_xboole_0(A_48, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_166])).
% 7.75/2.71  tff(c_30, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.75/2.71  tff(c_176, plain, (![A_48]: (k5_xboole_0(A_48, k1_xboole_0)=k4_xboole_0(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_30])).
% 7.75/2.71  tff(c_180, plain, (![A_48]: (k5_xboole_0(A_48, k1_xboole_0)=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_176])).
% 7.75/2.71  tff(c_38, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.75/2.71  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.75/2.71  tff(c_34, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.75/2.71  tff(c_17216, plain, (![A_7641, B_7642]: (k3_xboole_0(k1_tarski(A_7641), B_7642)=k1_xboole_0 | ~r2_hidden(A_7641, k4_xboole_0(k1_tarski(A_7641), B_7642)))), inference(superposition, [status(thm), theory('equality')], [c_16346, c_34])).
% 7.75/2.71  tff(c_17259, plain, (![D_6, B_2]: (k3_xboole_0(k1_tarski(D_6), B_2)=k1_xboole_0 | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k1_tarski(D_6)))), inference(resolution, [status(thm)], [c_2, c_17216])).
% 7.75/2.71  tff(c_17283, plain, (![D_7665, B_7666]: (k3_xboole_0(k1_tarski(D_7665), B_7666)=k1_xboole_0 | r2_hidden(D_7665, B_7666))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_17259])).
% 7.75/2.71  tff(c_17378, plain, (![D_7665, B_7666]: (k5_xboole_0(k1_tarski(D_7665), k1_xboole_0)=k4_xboole_0(k1_tarski(D_7665), B_7666) | r2_hidden(D_7665, B_7666))), inference(superposition, [status(thm), theory('equality')], [c_17283, c_30])).
% 7.75/2.71  tff(c_17482, plain, (![D_7689, B_7690]: (k4_xboole_0(k1_tarski(D_7689), B_7690)=k1_tarski(D_7689) | r2_hidden(D_7689, B_7690))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_17378])).
% 7.75/2.71  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.75/2.71  tff(c_17579, plain, (r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_17482, c_52])).
% 7.75/2.71  tff(c_17682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16520, c_17579])).
% 7.75/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.71  
% 7.75/2.71  Inference rules
% 7.75/2.71  ----------------------
% 7.75/2.71  #Ref     : 0
% 7.75/2.71  #Sup     : 2892
% 7.75/2.71  #Fact    : 14
% 7.75/2.71  #Define  : 0
% 7.75/2.71  #Split   : 5
% 7.75/2.71  #Chain   : 0
% 7.75/2.71  #Close   : 0
% 7.75/2.71  
% 7.75/2.71  Ordering : KBO
% 7.75/2.71  
% 7.75/2.71  Simplification rules
% 7.75/2.71  ----------------------
% 7.75/2.71  #Subsume      : 1071
% 7.75/2.71  #Demod        : 1138
% 7.75/2.71  #Tautology    : 658
% 7.75/2.71  #SimpNegUnit  : 18
% 7.75/2.71  #BackRed      : 1
% 7.75/2.71  
% 7.75/2.71  #Partial instantiations: 4355
% 7.75/2.71  #Strategies tried      : 1
% 7.75/2.71  
% 7.75/2.71  Timing (in seconds)
% 7.75/2.71  ----------------------
% 7.75/2.72  Preprocessing        : 0.28
% 7.75/2.72  Parsing              : 0.14
% 7.75/2.72  CNF conversion       : 0.02
% 7.75/2.72  Main loop            : 1.60
% 7.75/2.72  Inferencing          : 0.63
% 7.75/2.72  Reduction            : 0.44
% 7.75/2.72  Demodulation         : 0.30
% 7.75/2.72  BG Simplification    : 0.07
% 7.75/2.72  Subsumption          : 0.35
% 7.75/2.72  Abstraction          : 0.10
% 7.75/2.72  MUC search           : 0.00
% 7.75/2.72  Cooper               : 0.00
% 7.75/2.72  Total                : 1.92
% 7.75/2.72  Index Insertion      : 0.00
% 7.75/2.72  Index Deletion       : 0.00
% 7.75/2.72  Index Matching       : 0.00
% 7.75/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
