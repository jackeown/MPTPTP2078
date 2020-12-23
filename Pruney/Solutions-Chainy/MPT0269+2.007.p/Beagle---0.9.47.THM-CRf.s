%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:44 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 143 expanded)
%              Number of leaves         :   37 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 170 expanded)
%              Number of equality atoms :   31 (  95 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_tarski(A_54),B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_318,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_334,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_318])).

tff(c_106,plain,(
    ! [B_68,A_69] : k5_xboole_0(B_68,A_69) = k5_xboole_0(A_69,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_26])).

tff(c_30,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_497,plain,(
    ! [A_118,B_119,C_120] : k5_xboole_0(k5_xboole_0(A_118,B_119),C_120) = k5_xboole_0(A_118,k5_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_565,plain,(
    ! [A_25,C_120] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_120)) = k5_xboole_0(k1_xboole_0,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_497])).

tff(c_586,plain,(
    ! [A_121,C_122] : k5_xboole_0(A_121,k5_xboole_0(A_121,C_122)) = C_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_565])).

tff(c_999,plain,(
    ! [B_146,A_147] : k5_xboole_0(B_146,k4_xboole_0(B_146,A_147)) = k3_xboole_0(A_147,B_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_586])).

tff(c_1045,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_999])).

tff(c_1052,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1045])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1092,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_24])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1114,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1092,c_16])).

tff(c_1117,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1114])).

tff(c_1121,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1117])).

tff(c_50,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(k1_tarski(A_56),B_57)
      | r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_443,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_2'(A_110,B_111),k3_xboole_0(A_110,B_111))
      | r1_xboole_0(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_279,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_285,plain,(
    ! [B_2,A_1,C_87] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_87,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_463,plain,(
    ! [B_112,A_113] :
      ( ~ r1_xboole_0(B_112,A_113)
      | r1_xboole_0(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_443,c_285])).

tff(c_466,plain,(
    ! [B_57,A_56] :
      ( r1_xboole_0(B_57,k1_tarski(A_56))
      | r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_50,c_463])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_291,plain,(
    ! [A_88,B_89] :
      ( ~ r1_xboole_0(A_88,B_89)
      | v1_xboole_0(k3_xboole_0(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_8,c_279])).

tff(c_297,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(A_1,B_2)
      | v1_xboole_0(k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_291])).

tff(c_1074,plain,
    ( ~ r1_xboole_0('#skF_3',k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_297])).

tff(c_1165,plain,(
    ~ r1_xboole_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_1168,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_466,c_1165])).

tff(c_1172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1121,c_1168])).

tff(c_1173,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_10,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1199,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1173,c_10])).

tff(c_1203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:32:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  
% 3.24/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.24/1.47  
% 3.24/1.47  %Foreground sorts:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Background operators:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Foreground operators:
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.24/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.24/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.47  
% 3.24/1.49  tff(f_102, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.24/1.49  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.24/1.49  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.24/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.24/1.49  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.24/1.49  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.24/1.49  tff(f_69, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.24/1.49  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.24/1.49  tff(f_63, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.24/1.49  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.24/1.49  tff(f_92, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.24/1.49  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.24/1.49  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.24/1.49  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.24/1.49  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.24/1.49  tff(c_48, plain, (![A_54, B_55]: (r1_tarski(k1_tarski(A_54), B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.24/1.49  tff(c_52, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.24/1.49  tff(c_26, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.49  tff(c_56, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.24/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.49  tff(c_318, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.49  tff(c_334, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_318])).
% 3.24/1.49  tff(c_106, plain, (![B_68, A_69]: (k5_xboole_0(B_68, A_69)=k5_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.24/1.49  tff(c_122, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_106, c_26])).
% 3.24/1.49  tff(c_30, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.24/1.49  tff(c_497, plain, (![A_118, B_119, C_120]: (k5_xboole_0(k5_xboole_0(A_118, B_119), C_120)=k5_xboole_0(A_118, k5_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.49  tff(c_565, plain, (![A_25, C_120]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_120))=k5_xboole_0(k1_xboole_0, C_120))), inference(superposition, [status(thm), theory('equality')], [c_30, c_497])).
% 3.24/1.49  tff(c_586, plain, (![A_121, C_122]: (k5_xboole_0(A_121, k5_xboole_0(A_121, C_122))=C_122)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_565])).
% 3.24/1.49  tff(c_999, plain, (![B_146, A_147]: (k5_xboole_0(B_146, k4_xboole_0(B_146, A_147))=k3_xboole_0(A_147, B_146))), inference(superposition, [status(thm), theory('equality')], [c_334, c_586])).
% 3.24/1.49  tff(c_1045, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_999])).
% 3.24/1.49  tff(c_1052, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1045])).
% 3.24/1.49  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.24/1.49  tff(c_1092, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1052, c_24])).
% 3.24/1.49  tff(c_16, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.24/1.49  tff(c_1114, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1092, c_16])).
% 3.24/1.49  tff(c_1117, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_1114])).
% 3.24/1.49  tff(c_1121, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_1117])).
% 3.24/1.49  tff(c_50, plain, (![A_56, B_57]: (r1_xboole_0(k1_tarski(A_56), B_57) | r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.49  tff(c_443, plain, (![A_110, B_111]: (r2_hidden('#skF_2'(A_110, B_111), k3_xboole_0(A_110, B_111)) | r1_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.49  tff(c_279, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.49  tff(c_285, plain, (![B_2, A_1, C_87]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_87, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 3.24/1.49  tff(c_463, plain, (![B_112, A_113]: (~r1_xboole_0(B_112, A_113) | r1_xboole_0(A_113, B_112))), inference(resolution, [status(thm)], [c_443, c_285])).
% 3.24/1.49  tff(c_466, plain, (![B_57, A_56]: (r1_xboole_0(B_57, k1_tarski(A_56)) | r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_50, c_463])).
% 3.24/1.49  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.49  tff(c_291, plain, (![A_88, B_89]: (~r1_xboole_0(A_88, B_89) | v1_xboole_0(k3_xboole_0(A_88, B_89)))), inference(resolution, [status(thm)], [c_8, c_279])).
% 3.24/1.49  tff(c_297, plain, (![A_1, B_2]: (~r1_xboole_0(A_1, B_2) | v1_xboole_0(k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_291])).
% 3.24/1.49  tff(c_1074, plain, (~r1_xboole_0('#skF_3', k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_297])).
% 3.24/1.49  tff(c_1165, plain, (~r1_xboole_0('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_1074])).
% 3.24/1.49  tff(c_1168, plain, (r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_466, c_1165])).
% 3.24/1.49  tff(c_1172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1121, c_1168])).
% 3.24/1.49  tff(c_1173, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1074])).
% 3.24/1.49  tff(c_10, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.49  tff(c_1199, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1173, c_10])).
% 3.24/1.49  tff(c_1203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1199])).
% 3.24/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  Inference rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Ref     : 0
% 3.24/1.49  #Sup     : 283
% 3.24/1.49  #Fact    : 0
% 3.24/1.49  #Define  : 0
% 3.24/1.49  #Split   : 1
% 3.24/1.49  #Chain   : 0
% 3.24/1.49  #Close   : 0
% 3.24/1.49  
% 3.24/1.49  Ordering : KBO
% 3.24/1.49  
% 3.24/1.49  Simplification rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Subsume      : 20
% 3.24/1.49  #Demod        : 104
% 3.24/1.49  #Tautology    : 171
% 3.24/1.49  #SimpNegUnit  : 4
% 3.24/1.49  #BackRed      : 0
% 3.24/1.49  
% 3.24/1.49  #Partial instantiations: 0
% 3.24/1.49  #Strategies tried      : 1
% 3.24/1.49  
% 3.24/1.49  Timing (in seconds)
% 3.24/1.49  ----------------------
% 3.24/1.49  Preprocessing        : 0.33
% 3.24/1.49  Parsing              : 0.18
% 3.24/1.49  CNF conversion       : 0.02
% 3.24/1.49  Main loop            : 0.37
% 3.24/1.49  Inferencing          : 0.13
% 3.24/1.49  Reduction            : 0.13
% 3.24/1.49  Demodulation         : 0.11
% 3.24/1.49  BG Simplification    : 0.02
% 3.24/1.49  Subsumption          : 0.06
% 3.24/1.49  Abstraction          : 0.02
% 3.24/1.49  MUC search           : 0.00
% 3.24/1.49  Cooper               : 0.00
% 3.24/1.49  Total                : 0.73
% 3.24/1.49  Index Insertion      : 0.00
% 3.24/1.49  Index Deletion       : 0.00
% 3.24/1.49  Index Matching       : 0.00
% 3.24/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
