%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 100 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :   95 ( 131 expanded)
%              Number of equality atoms :   34 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_64,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_3'(A_12,B_13,C_14),A_12)
      | r2_hidden('#skF_4'(A_12,B_13,C_14),C_14)
      | k4_xboole_0(A_12,B_13) = C_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1102,plain,(
    ! [A_157,B_158,C_159] :
      ( ~ r2_hidden('#skF_3'(A_157,B_158,C_159),B_158)
      | r2_hidden('#skF_4'(A_157,B_158,C_159),C_159)
      | k4_xboole_0(A_157,B_158) = C_159 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1214,plain,(
    ! [A_171,C_172] :
      ( r2_hidden('#skF_4'(A_171,A_171,C_172),C_172)
      | k4_xboole_0(A_171,A_171) = C_172 ) ),
    inference(resolution,[status(thm)],[c_30,c_1102])).

tff(c_38,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_183,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | ~ r1_tarski(k1_tarski(A_50),B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_194,plain,(
    ! [A_54] : r2_hidden(A_54,k1_tarski(A_54)) ),
    inference(resolution,[status(thm)],[c_38,c_183])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_198,plain,(
    ! [A_54] : ~ v1_xboole_0(k1_tarski(A_54)) ),
    inference(resolution,[status(thm)],[c_194,c_4])).

tff(c_58,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_516,plain,(
    ! [C_101,B_102,A_103] :
      ( r2_hidden(C_101,B_102)
      | ~ r2_hidden(C_101,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_687,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_1'(A_119),B_120)
      | ~ r1_tarski(A_119,B_120)
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_6,c_516])).

tff(c_96,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_48] : k2_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_42])).

tff(c_270,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_277,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_112])).

tff(c_286,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = B_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_277])).

tff(c_470,plain,(
    ! [D_91,B_92,A_93] :
      ( ~ r2_hidden(D_91,B_92)
      | ~ r2_hidden(D_91,k4_xboole_0(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_476,plain,(
    ! [D_91,B_70] :
      ( ~ r2_hidden(D_91,k1_xboole_0)
      | ~ r2_hidden(D_91,B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_470])).

tff(c_773,plain,(
    ! [A_128,B_129] :
      ( ~ r2_hidden('#skF_1'(A_128),B_129)
      | ~ r1_tarski(A_128,k1_xboole_0)
      | v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_687,c_476])).

tff(c_796,plain,(
    ! [A_132] :
      ( ~ r1_tarski(A_132,k1_xboole_0)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_6,c_773])).

tff(c_808,plain,(
    ! [A_37] :
      ( v1_xboole_0(k1_tarski(A_37))
      | ~ r2_hidden(A_37,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_58,c_796])).

tff(c_818,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_808])).

tff(c_1236,plain,(
    ! [A_171] : k4_xboole_0(A_171,A_171) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1214,c_818])).

tff(c_189,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_193,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_38,c_189])).

tff(c_316,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_325,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k4_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_316])).

tff(c_209,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_tarski(A_57),B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_660,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(k1_tarski(A_117),B_118) = k1_tarski(A_117)
      | ~ r2_hidden(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_209,c_44])).

tff(c_40,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_666,plain,(
    ! [A_117,B_118] :
      ( k5_xboole_0(k1_tarski(A_117),k1_tarski(A_117)) = k4_xboole_0(k1_tarski(A_117),B_118)
      | ~ r2_hidden(A_117,B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_40])).

tff(c_679,plain,(
    ! [A_117,B_118] :
      ( k4_xboole_0(k1_tarski(A_117),k1_tarski(A_117)) = k4_xboole_0(k1_tarski(A_117),B_118)
      | ~ r2_hidden(A_117,B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_666])).

tff(c_13555,plain,(
    ! [A_607,B_608] :
      ( k4_xboole_0(k1_tarski(A_607),B_608) = k1_xboole_0
      | ~ r2_hidden(A_607,B_608) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1236,c_679])).

tff(c_46,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_13974,plain,(
    ! [B_608,A_607] :
      ( k2_xboole_0(B_608,k1_tarski(A_607)) = k2_xboole_0(B_608,k1_xboole_0)
      | ~ r2_hidden(A_607,B_608) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13555,c_46])).

tff(c_14227,plain,(
    ! [B_611,A_612] :
      ( k2_xboole_0(B_611,k1_tarski(A_612)) = B_611
      | ~ r2_hidden(A_612,B_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_13974])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_14255,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_14227,c_66])).

tff(c_14290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:26:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.04/2.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/2.94  
% 8.04/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/2.95  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 8.04/2.95  
% 8.04/2.95  %Foreground sorts:
% 8.04/2.95  
% 8.04/2.95  
% 8.04/2.95  %Background operators:
% 8.04/2.95  
% 8.04/2.95  
% 8.04/2.95  %Foreground operators:
% 8.04/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.04/2.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.04/2.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.04/2.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.04/2.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.04/2.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.04/2.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.04/2.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.04/2.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.04/2.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.04/2.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.04/2.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.04/2.95  tff('#skF_5', type, '#skF_5': $i).
% 8.04/2.95  tff('#skF_6', type, '#skF_6': $i).
% 8.04/2.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.04/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.04/2.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.04/2.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.04/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.04/2.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.04/2.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.04/2.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.04/2.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.04/2.95  
% 8.04/2.96  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.04/2.96  tff(f_61, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.04/2.96  tff(f_50, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.04/2.96  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.04/2.96  tff(f_79, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.04/2.96  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.04/2.96  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.04/2.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.04/2.96  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.04/2.96  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.04/2.96  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.04/2.96  tff(c_64, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.04/2.96  tff(c_42, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.04/2.96  tff(c_30, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_3'(A_12, B_13, C_14), A_12) | r2_hidden('#skF_4'(A_12, B_13, C_14), C_14) | k4_xboole_0(A_12, B_13)=C_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.04/2.96  tff(c_1102, plain, (![A_157, B_158, C_159]: (~r2_hidden('#skF_3'(A_157, B_158, C_159), B_158) | r2_hidden('#skF_4'(A_157, B_158, C_159), C_159) | k4_xboole_0(A_157, B_158)=C_159)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.04/2.96  tff(c_1214, plain, (![A_171, C_172]: (r2_hidden('#skF_4'(A_171, A_171, C_172), C_172) | k4_xboole_0(A_171, A_171)=C_172)), inference(resolution, [status(thm)], [c_30, c_1102])).
% 8.04/2.96  tff(c_38, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.04/2.96  tff(c_183, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | ~r1_tarski(k1_tarski(A_50), B_51))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.04/2.96  tff(c_194, plain, (![A_54]: (r2_hidden(A_54, k1_tarski(A_54)))), inference(resolution, [status(thm)], [c_38, c_183])).
% 8.04/2.96  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.04/2.96  tff(c_198, plain, (![A_54]: (~v1_xboole_0(k1_tarski(A_54)))), inference(resolution, [status(thm)], [c_194, c_4])).
% 8.04/2.96  tff(c_58, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.04/2.96  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.04/2.96  tff(c_516, plain, (![C_101, B_102, A_103]: (r2_hidden(C_101, B_102) | ~r2_hidden(C_101, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.04/2.96  tff(c_687, plain, (![A_119, B_120]: (r2_hidden('#skF_1'(A_119), B_120) | ~r1_tarski(A_119, B_120) | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_6, c_516])).
% 8.04/2.96  tff(c_96, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.04/2.96  tff(c_112, plain, (![A_48]: (k2_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_96, c_42])).
% 8.04/2.96  tff(c_270, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.04/2.96  tff(c_277, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_270, c_112])).
% 8.04/2.96  tff(c_286, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=B_70)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_277])).
% 8.04/2.96  tff(c_470, plain, (![D_91, B_92, A_93]: (~r2_hidden(D_91, B_92) | ~r2_hidden(D_91, k4_xboole_0(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.04/2.96  tff(c_476, plain, (![D_91, B_70]: (~r2_hidden(D_91, k1_xboole_0) | ~r2_hidden(D_91, B_70))), inference(superposition, [status(thm), theory('equality')], [c_286, c_470])).
% 8.04/2.96  tff(c_773, plain, (![A_128, B_129]: (~r2_hidden('#skF_1'(A_128), B_129) | ~r1_tarski(A_128, k1_xboole_0) | v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_687, c_476])).
% 8.04/2.96  tff(c_796, plain, (![A_132]: (~r1_tarski(A_132, k1_xboole_0) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_6, c_773])).
% 8.04/2.96  tff(c_808, plain, (![A_37]: (v1_xboole_0(k1_tarski(A_37)) | ~r2_hidden(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_796])).
% 8.04/2.96  tff(c_818, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_198, c_808])).
% 8.04/2.96  tff(c_1236, plain, (![A_171]: (k4_xboole_0(A_171, A_171)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1214, c_818])).
% 8.04/2.96  tff(c_189, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.04/2.96  tff(c_193, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_38, c_189])).
% 8.04/2.96  tff(c_316, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.04/2.96  tff(c_325, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k4_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_193, c_316])).
% 8.04/2.96  tff(c_209, plain, (![A_57, B_58]: (r1_tarski(k1_tarski(A_57), B_58) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.04/2.96  tff(c_44, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.04/2.96  tff(c_660, plain, (![A_117, B_118]: (k3_xboole_0(k1_tarski(A_117), B_118)=k1_tarski(A_117) | ~r2_hidden(A_117, B_118))), inference(resolution, [status(thm)], [c_209, c_44])).
% 8.04/2.96  tff(c_40, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.04/2.96  tff(c_666, plain, (![A_117, B_118]: (k5_xboole_0(k1_tarski(A_117), k1_tarski(A_117))=k4_xboole_0(k1_tarski(A_117), B_118) | ~r2_hidden(A_117, B_118))), inference(superposition, [status(thm), theory('equality')], [c_660, c_40])).
% 8.04/2.96  tff(c_679, plain, (![A_117, B_118]: (k4_xboole_0(k1_tarski(A_117), k1_tarski(A_117))=k4_xboole_0(k1_tarski(A_117), B_118) | ~r2_hidden(A_117, B_118))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_666])).
% 8.04/2.96  tff(c_13555, plain, (![A_607, B_608]: (k4_xboole_0(k1_tarski(A_607), B_608)=k1_xboole_0 | ~r2_hidden(A_607, B_608))), inference(demodulation, [status(thm), theory('equality')], [c_1236, c_679])).
% 8.04/2.96  tff(c_46, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.04/2.96  tff(c_13974, plain, (![B_608, A_607]: (k2_xboole_0(B_608, k1_tarski(A_607))=k2_xboole_0(B_608, k1_xboole_0) | ~r2_hidden(A_607, B_608))), inference(superposition, [status(thm), theory('equality')], [c_13555, c_46])).
% 8.04/2.96  tff(c_14227, plain, (![B_611, A_612]: (k2_xboole_0(B_611, k1_tarski(A_612))=B_611 | ~r2_hidden(A_612, B_611))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_13974])).
% 8.04/2.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.04/2.96  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.04/2.96  tff(c_66, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 8.04/2.96  tff(c_14255, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_14227, c_66])).
% 8.04/2.96  tff(c_14290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_14255])).
% 8.04/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/2.96  
% 8.04/2.96  Inference rules
% 8.04/2.96  ----------------------
% 8.04/2.96  #Ref     : 0
% 8.04/2.96  #Sup     : 3545
% 8.04/2.96  #Fact    : 0
% 8.04/2.96  #Define  : 0
% 8.04/2.96  #Split   : 8
% 8.04/2.96  #Chain   : 0
% 8.04/2.96  #Close   : 0
% 8.04/2.96  
% 8.04/2.96  Ordering : KBO
% 8.04/2.96  
% 8.04/2.96  Simplification rules
% 8.04/2.96  ----------------------
% 8.04/2.96  #Subsume      : 1832
% 8.04/2.96  #Demod        : 1613
% 8.04/2.96  #Tautology    : 830
% 8.04/2.96  #SimpNegUnit  : 123
% 8.04/2.96  #BackRed      : 34
% 8.04/2.96  
% 8.04/2.96  #Partial instantiations: 0
% 8.04/2.96  #Strategies tried      : 1
% 8.04/2.96  
% 8.04/2.96  Timing (in seconds)
% 8.04/2.96  ----------------------
% 8.04/2.96  Preprocessing        : 0.35
% 8.04/2.96  Parsing              : 0.18
% 8.04/2.96  CNF conversion       : 0.03
% 8.04/2.96  Main loop            : 1.79
% 8.04/2.97  Inferencing          : 0.54
% 8.04/2.97  Reduction            : 0.59
% 8.04/2.97  Demodulation         : 0.42
% 8.04/2.97  BG Simplification    : 0.05
% 8.04/2.97  Subsumption          : 0.51
% 8.04/2.97  Abstraction          : 0.08
% 8.04/2.97  MUC search           : 0.00
% 8.04/2.97  Cooper               : 0.00
% 8.04/2.97  Total                : 2.17
% 8.04/2.97  Index Insertion      : 0.00
% 8.04/2.97  Index Deletion       : 0.00
% 8.04/2.97  Index Matching       : 0.00
% 8.04/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
