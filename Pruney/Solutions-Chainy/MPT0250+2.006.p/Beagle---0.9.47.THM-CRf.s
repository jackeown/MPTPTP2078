%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 51.69s
% Output     : CNFRefutation 51.69s
% Verified   : 
% Statistics : Number of formulae       :   80 (  97 expanded)
%              Number of leaves         :   38 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 140 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_5

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_106,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_104,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_114,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
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

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_172,plain,(
    ! [A_68,B_69] : k1_enumset1(A_68,A_68,B_69) = k2_tarski(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_58,plain,(
    ! [E_34,A_28,C_30] : r2_hidden(E_34,k1_enumset1(A_28,E_34,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_181,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_58])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    ! [E_34,A_28,B_29] : r2_hidden(E_34,k1_enumset1(A_28,B_29,E_34)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_190,plain,(
    ! [B_70,A_71] : r2_hidden(B_70,k2_tarski(A_71,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_56])).

tff(c_199,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_190])).

tff(c_40,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_765,plain,(
    ! [A_138,C_139,B_140] :
      ( r2_hidden(A_138,C_139)
      | ~ r2_hidden(A_138,B_140)
      | r2_hidden(A_138,k5_xboole_0(B_140,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_771,plain,(
    ! [A_138,A_17,B_18] :
      ( r2_hidden(A_138,k3_xboole_0(A_17,B_18))
      | ~ r2_hidden(A_138,A_17)
      | r2_hidden(A_138,k4_xboole_0(A_17,B_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_765])).

tff(c_52,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_216,plain,(
    ! [A_75,B_76] : k3_tarski(k2_tarski(A_75,B_76)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_273,plain,(
    ! [B_80,A_81] : k3_tarski(k2_tarski(B_80,A_81)) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_216])).

tff(c_88,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_279,plain,(
    ! [B_80,A_81] : k2_xboole_0(B_80,A_81) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_88])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_252,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(A_78,B_79) = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_256,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski('#skF_6'),'#skF_7'),'#skF_7') = k2_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_252])).

tff(c_267,plain,(
    k3_xboole_0('#skF_7',k2_xboole_0(k1_tarski('#skF_6'),'#skF_7')) = k2_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_256])).

tff(c_535,plain,(
    k3_xboole_0('#skF_7',k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) = k2_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_267])).

tff(c_36,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_454,plain,(
    ! [D_104,A_105,B_106] :
      ( r2_hidden(D_104,A_105)
      | ~ r2_hidden(D_104,k3_xboole_0(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_472,plain,(
    ! [A_12,A_105,B_106] :
      ( r2_hidden('#skF_3'(A_12,k3_xboole_0(A_105,B_106)),A_105)
      | r1_xboole_0(A_12,k3_xboole_0(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_36,c_454])).

tff(c_38,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_587,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,B_118)
      | ~ r2_hidden(C_119,A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_600,plain,(
    ! [C_120,B_121,A_122] :
      ( ~ r2_hidden(C_120,B_121)
      | ~ r2_hidden(C_120,k4_xboole_0(A_122,B_121)) ) ),
    inference(resolution,[status(thm)],[c_50,c_587])).

tff(c_8077,plain,(
    ! [A_19682,B_19683,B_19684] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_19682,B_19683),B_19684),B_19683)
      | r1_xboole_0(k4_xboole_0(A_19682,B_19683),B_19684) ) ),
    inference(resolution,[status(thm)],[c_38,c_600])).

tff(c_8163,plain,(
    ! [A_19964,A_19965,B_19966] : r1_xboole_0(k4_xboole_0(A_19964,A_19965),k3_xboole_0(A_19965,B_19966)) ),
    inference(resolution,[status(thm)],[c_472,c_8077])).

tff(c_8277,plain,(
    ! [A_20246] : r1_xboole_0(k4_xboole_0(A_20246,'#skF_7'),k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_8163])).

tff(c_46,plain,(
    ! [A_21,C_23,B_22] :
      ( r1_xboole_0(A_21,C_23)
      | ~ r1_xboole_0(A_21,k2_xboole_0(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8297,plain,(
    ! [A_20385] : r1_xboole_0(k4_xboole_0(A_20385,'#skF_7'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_8277,c_46])).

tff(c_34,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8305,plain,(
    ! [C_20524,A_20525] :
      ( ~ r2_hidden(C_20524,k1_tarski('#skF_6'))
      | ~ r2_hidden(C_20524,k4_xboole_0(A_20525,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_8297,c_34])).

tff(c_213487,plain,(
    ! [A_236537,A_236538] :
      ( ~ r2_hidden(A_236537,k1_tarski('#skF_6'))
      | r2_hidden(A_236537,k3_xboole_0(A_236538,'#skF_7'))
      | ~ r2_hidden(A_236537,A_236538) ) ),
    inference(resolution,[status(thm)],[c_771,c_8305])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_214051,plain,(
    ! [A_237371,A_237372] :
      ( r2_hidden(A_237371,'#skF_7')
      | ~ r2_hidden(A_237371,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_237371,A_237372) ) ),
    inference(resolution,[status(thm)],[c_213487,c_6])).

tff(c_214258,plain,(
    ! [A_237372] :
      ( r2_hidden('#skF_6','#skF_7')
      | ~ r2_hidden('#skF_6',A_237372) ) ),
    inference(resolution,[status(thm)],[c_199,c_214051])).

tff(c_214330,plain,(
    ! [A_237787] : ~ r2_hidden('#skF_6',A_237787) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_214258])).

tff(c_214485,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_181,c_214330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 51.69/39.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.69/39.93  
% 51.69/39.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.69/39.93  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_5
% 51.69/39.93  
% 51.69/39.93  %Foreground sorts:
% 51.69/39.93  
% 51.69/39.93  
% 51.69/39.93  %Background operators:
% 51.69/39.93  
% 51.69/39.93  
% 51.69/39.93  %Foreground operators:
% 51.69/39.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 51.69/39.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 51.69/39.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 51.69/39.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 51.69/39.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 51.69/39.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 51.69/39.93  tff('#skF_7', type, '#skF_7': $i).
% 51.69/39.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 51.69/39.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 51.69/39.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 51.69/39.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 51.69/39.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 51.69/39.93  tff('#skF_6', type, '#skF_6': $i).
% 51.69/39.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 51.69/39.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 51.69/39.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 51.69/39.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 51.69/39.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 51.69/39.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 51.69/39.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 51.69/39.93  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 51.69/39.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 51.69/39.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 51.69/39.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 51.69/39.93  
% 51.69/39.94  tff(f_106, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 51.69/39.94  tff(f_102, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 51.69/39.94  tff(f_119, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 51.69/39.94  tff(f_104, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 51.69/39.94  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 51.69/39.94  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 51.69/39.94  tff(f_87, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 51.69/39.94  tff(f_114, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 51.69/39.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 51.69/39.94  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 51.69/39.94  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 51.69/39.94  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 51.69/39.94  tff(f_85, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 51.69/39.94  tff(f_83, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 51.69/39.94  tff(c_172, plain, (![A_68, B_69]: (k1_enumset1(A_68, A_68, B_69)=k2_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_106])).
% 51.69/39.94  tff(c_58, plain, (![E_34, A_28, C_30]: (r2_hidden(E_34, k1_enumset1(A_28, E_34, C_30)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 51.69/39.94  tff(c_181, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_58])).
% 51.69/39.94  tff(c_90, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_119])).
% 51.69/39.94  tff(c_78, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_104])).
% 51.69/39.94  tff(c_56, plain, (![E_34, A_28, B_29]: (r2_hidden(E_34, k1_enumset1(A_28, B_29, E_34)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 51.69/39.94  tff(c_190, plain, (![B_70, A_71]: (r2_hidden(B_70, k2_tarski(A_71, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_56])).
% 51.69/39.94  tff(c_199, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_190])).
% 51.69/39.94  tff(c_40, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 51.69/39.94  tff(c_765, plain, (![A_138, C_139, B_140]: (r2_hidden(A_138, C_139) | ~r2_hidden(A_138, B_140) | r2_hidden(A_138, k5_xboole_0(B_140, C_139)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 51.69/39.94  tff(c_771, plain, (![A_138, A_17, B_18]: (r2_hidden(A_138, k3_xboole_0(A_17, B_18)) | ~r2_hidden(A_138, A_17) | r2_hidden(A_138, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_765])).
% 51.69/39.94  tff(c_52, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 51.69/39.94  tff(c_216, plain, (![A_75, B_76]: (k3_tarski(k2_tarski(A_75, B_76))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_114])).
% 51.69/39.94  tff(c_273, plain, (![B_80, A_81]: (k3_tarski(k2_tarski(B_80, A_81))=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_52, c_216])).
% 51.69/39.94  tff(c_88, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_114])).
% 51.69/39.94  tff(c_279, plain, (![B_80, A_81]: (k2_xboole_0(B_80, A_81)=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_273, c_88])).
% 51.69/39.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 51.69/39.94  tff(c_92, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_119])).
% 51.69/39.94  tff(c_252, plain, (![A_78, B_79]: (k3_xboole_0(A_78, B_79)=A_78 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_67])).
% 51.69/39.94  tff(c_256, plain, (k3_xboole_0(k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'), '#skF_7')=k2_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_92, c_252])).
% 51.69/39.94  tff(c_267, plain, (k3_xboole_0('#skF_7', k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'))=k2_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2, c_256])).
% 51.69/39.94  tff(c_535, plain, (k3_xboole_0('#skF_7', k2_xboole_0('#skF_7', k1_tarski('#skF_6')))=k2_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_267])).
% 51.69/39.94  tff(c_36, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 51.69/39.94  tff(c_454, plain, (![D_104, A_105, B_106]: (r2_hidden(D_104, A_105) | ~r2_hidden(D_104, k3_xboole_0(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 51.69/39.94  tff(c_472, plain, (![A_12, A_105, B_106]: (r2_hidden('#skF_3'(A_12, k3_xboole_0(A_105, B_106)), A_105) | r1_xboole_0(A_12, k3_xboole_0(A_105, B_106)))), inference(resolution, [status(thm)], [c_36, c_454])).
% 51.69/39.94  tff(c_38, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 51.69/39.94  tff(c_50, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 51.69/39.94  tff(c_587, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, B_118) | ~r2_hidden(C_119, A_117))), inference(cnfTransformation, [status(thm)], [f_61])).
% 51.69/39.94  tff(c_600, plain, (![C_120, B_121, A_122]: (~r2_hidden(C_120, B_121) | ~r2_hidden(C_120, k4_xboole_0(A_122, B_121)))), inference(resolution, [status(thm)], [c_50, c_587])).
% 51.69/39.94  tff(c_8077, plain, (![A_19682, B_19683, B_19684]: (~r2_hidden('#skF_3'(k4_xboole_0(A_19682, B_19683), B_19684), B_19683) | r1_xboole_0(k4_xboole_0(A_19682, B_19683), B_19684))), inference(resolution, [status(thm)], [c_38, c_600])).
% 51.69/39.94  tff(c_8163, plain, (![A_19964, A_19965, B_19966]: (r1_xboole_0(k4_xboole_0(A_19964, A_19965), k3_xboole_0(A_19965, B_19966)))), inference(resolution, [status(thm)], [c_472, c_8077])).
% 51.69/39.94  tff(c_8277, plain, (![A_20246]: (r1_xboole_0(k4_xboole_0(A_20246, '#skF_7'), k2_xboole_0('#skF_7', k1_tarski('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_535, c_8163])).
% 51.69/39.94  tff(c_46, plain, (![A_21, C_23, B_22]: (r1_xboole_0(A_21, C_23) | ~r1_xboole_0(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 51.69/39.94  tff(c_8297, plain, (![A_20385]: (r1_xboole_0(k4_xboole_0(A_20385, '#skF_7'), k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_8277, c_46])).
% 51.69/39.94  tff(c_34, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, B_13) | ~r2_hidden(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 51.69/39.94  tff(c_8305, plain, (![C_20524, A_20525]: (~r2_hidden(C_20524, k1_tarski('#skF_6')) | ~r2_hidden(C_20524, k4_xboole_0(A_20525, '#skF_7')))), inference(resolution, [status(thm)], [c_8297, c_34])).
% 51.69/39.94  tff(c_213487, plain, (![A_236537, A_236538]: (~r2_hidden(A_236537, k1_tarski('#skF_6')) | r2_hidden(A_236537, k3_xboole_0(A_236538, '#skF_7')) | ~r2_hidden(A_236537, A_236538))), inference(resolution, [status(thm)], [c_771, c_8305])).
% 51.69/39.94  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 51.69/39.94  tff(c_214051, plain, (![A_237371, A_237372]: (r2_hidden(A_237371, '#skF_7') | ~r2_hidden(A_237371, k1_tarski('#skF_6')) | ~r2_hidden(A_237371, A_237372))), inference(resolution, [status(thm)], [c_213487, c_6])).
% 51.69/39.94  tff(c_214258, plain, (![A_237372]: (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', A_237372))), inference(resolution, [status(thm)], [c_199, c_214051])).
% 51.69/39.94  tff(c_214330, plain, (![A_237787]: (~r2_hidden('#skF_6', A_237787))), inference(negUnitSimplification, [status(thm)], [c_90, c_214258])).
% 51.69/39.94  tff(c_214485, plain, $false, inference(resolution, [status(thm)], [c_181, c_214330])).
% 51.69/39.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.69/39.94  
% 51.69/39.94  Inference rules
% 51.69/39.94  ----------------------
% 51.69/39.94  #Ref     : 0
% 51.69/39.94  #Sup     : 41276
% 51.69/39.94  #Fact    : 296
% 51.69/39.94  #Define  : 0
% 51.69/39.94  #Split   : 0
% 51.69/39.94  #Chain   : 0
% 51.69/39.94  #Close   : 0
% 51.69/39.94  
% 51.69/39.94  Ordering : KBO
% 51.69/39.94  
% 51.69/39.94  Simplification rules
% 51.69/39.94  ----------------------
% 51.69/39.94  #Subsume      : 15803
% 51.69/39.94  #Demod        : 7153
% 51.69/39.94  #Tautology    : 9933
% 51.69/39.94  #SimpNegUnit  : 2508
% 51.69/39.94  #BackRed      : 6
% 51.69/39.94  
% 51.69/39.94  #Partial instantiations: 92466
% 51.69/39.94  #Strategies tried      : 1
% 51.69/39.94  
% 51.69/39.94  Timing (in seconds)
% 51.69/39.94  ----------------------
% 51.69/39.95  Preprocessing        : 0.34
% 51.69/39.95  Parsing              : 0.17
% 51.69/39.95  CNF conversion       : 0.03
% 51.69/39.95  Main loop            : 38.84
% 51.69/39.95  Inferencing          : 6.92
% 51.69/39.95  Reduction            : 16.34
% 51.69/39.95  Demodulation         : 14.14
% 51.69/39.95  BG Simplification    : 0.69
% 51.69/39.95  Subsumption          : 13.20
% 51.69/39.95  Abstraction          : 1.39
% 51.69/39.95  MUC search           : 0.00
% 51.69/39.95  Cooper               : 0.00
% 51.69/39.95  Total                : 39.21
% 51.69/39.95  Index Insertion      : 0.00
% 51.69/39.95  Index Deletion       : 0.00
% 51.69/39.95  Index Matching       : 0.00
% 51.69/39.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
