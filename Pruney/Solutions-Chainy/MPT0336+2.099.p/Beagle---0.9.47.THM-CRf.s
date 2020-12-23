%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:13 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 121 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 240 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_87,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_74,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_81,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    ! [D_24,A_19] : r2_hidden(D_24,k2_tarski(A_19,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_87,plain,(
    ! [A_41] : r2_hidden(A_41,k1_tarski(A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_40])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_7'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_347,plain,(
    ! [B_90,A_91] :
      ( k1_tarski(B_90) = A_91
      | k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,k1_tarski(B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_357,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_9')
    | k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_347])).

tff(c_442,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_724,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,k1_xboole_0)
      | ~ r2_hidden(D_123,'#skF_7')
      | ~ r2_hidden(D_123,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_2])).

tff(c_239,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_3'(A_70,B_71),B_71)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_106])).

tff(c_214,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,A_65)
      | ~ r2_hidden(D_64,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_224,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,'#skF_8')
      | ~ r2_hidden(D_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_214])).

tff(c_253,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_3'(A_70,k1_xboole_0),'#skF_8')
      | r1_xboole_0(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_239,c_224])).

tff(c_98,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,A_44)
      | ~ r1_xboole_0(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_98])).

tff(c_113,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_106])).

tff(c_221,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,'#skF_7')
      | ~ r2_hidden(D_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_214])).

tff(c_252,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_3'(A_70,k1_xboole_0),'#skF_7')
      | r1_xboole_0(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_239,c_221])).

tff(c_362,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,B_93)
      | ~ r2_hidden(C_94,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_375,plain,(
    ! [C_95] :
      ( ~ r2_hidden(C_95,'#skF_7')
      | ~ r2_hidden(C_95,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_72,c_362])).

tff(c_571,plain,(
    ! [A_108] :
      ( ~ r2_hidden('#skF_3'(A_108,k1_xboole_0),'#skF_8')
      | r1_xboole_0(A_108,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_252,c_375])).

tff(c_591,plain,(
    ! [A_109] : r1_xboole_0(A_109,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_253,c_571])).

tff(c_26,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_599,plain,(
    ! [C_15,A_109] :
      ( ~ r2_hidden(C_15,k1_xboole_0)
      | ~ r2_hidden(C_15,A_109) ) ),
    inference(resolution,[status(thm)],[c_591,c_26])).

tff(c_953,plain,(
    ! [D_156,A_157] :
      ( ~ r2_hidden(D_156,A_157)
      | ~ r2_hidden(D_156,'#skF_7')
      | ~ r2_hidden(D_156,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_724,c_599])).

tff(c_984,plain,(
    ! [A_158] :
      ( ~ r2_hidden(A_158,'#skF_7')
      | ~ r2_hidden(A_158,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_87,c_953])).

tff(c_1002,plain,(
    ! [A_159] :
      ( ~ r2_hidden('#skF_3'(A_159,'#skF_7'),'#skF_6')
      | r1_xboole_0(A_159,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_28,c_984])).

tff(c_1007,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_1002])).

tff(c_24,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1024,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1007,c_24])).

tff(c_512,plain,(
    ! [A_100,C_101,B_102] :
      ( ~ r1_xboole_0(A_100,C_101)
      | ~ r1_xboole_0(A_100,B_102)
      | r1_xboole_0(A_100,k2_xboole_0(B_102,C_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4049,plain,(
    ! [B_7790,C_7791,A_7792] :
      ( r1_xboole_0(k2_xboole_0(B_7790,C_7791),A_7792)
      | ~ r1_xboole_0(A_7792,C_7791)
      | ~ r1_xboole_0(A_7792,B_7790) ) ),
    inference(resolution,[status(thm)],[c_512,c_24])).

tff(c_70,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_6','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4071,plain,
    ( ~ r1_xboole_0('#skF_7','#skF_8')
    | ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_4049,c_70])).

tff(c_4086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_101,c_4071])).

tff(c_4087,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_9') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4152,plain,(
    ! [D_7852] :
      ( r2_hidden(D_7852,'#skF_7')
      | ~ r2_hidden(D_7852,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4087,c_4])).

tff(c_4167,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_87,c_4152])).

tff(c_374,plain,(
    ! [C_94] :
      ( ~ r2_hidden(C_94,'#skF_7')
      | ~ r2_hidden(C_94,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_72,c_362])).

tff(c_4192,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_4167,c_374])).

tff(c_4196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.96  
% 5.01/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8
% 5.01/1.96  
% 5.01/1.96  %Foreground sorts:
% 5.01/1.96  
% 5.01/1.96  
% 5.01/1.96  %Background operators:
% 5.01/1.96  
% 5.01/1.96  
% 5.01/1.96  %Foreground operators:
% 5.01/1.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.01/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/1.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.01/1.96  tff('#skF_7', type, '#skF_7': $i).
% 5.01/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.01/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.01/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.01/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.01/1.96  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.01/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.01/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.01/1.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.01/1.96  tff('#skF_9', type, '#skF_9': $i).
% 5.01/1.96  tff('#skF_8', type, '#skF_8': $i).
% 5.01/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.01/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.01/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/1.96  
% 5.28/1.98  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.28/1.98  tff(f_87, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.28/1.98  tff(f_85, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 5.28/1.98  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.28/1.98  tff(f_97, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.28/1.98  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.28/1.98  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.28/1.98  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.28/1.98  tff(f_76, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.28/1.98  tff(c_74, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.28/1.98  tff(c_81, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.28/1.98  tff(c_40, plain, (![D_24, A_19]: (r2_hidden(D_24, k2_tarski(A_19, D_24)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/1.98  tff(c_87, plain, (![A_41]: (r2_hidden(A_41, k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_40])).
% 5.28/1.98  tff(c_30, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.28/1.98  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.28/1.98  tff(c_76, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.28/1.98  tff(c_347, plain, (![B_90, A_91]: (k1_tarski(B_90)=A_91 | k1_xboole_0=A_91 | ~r1_tarski(A_91, k1_tarski(B_90)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.28/1.98  tff(c_357, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_9') | k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_347])).
% 5.28/1.98  tff(c_442, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_357])).
% 5.28/1.98  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.28/1.98  tff(c_724, plain, (![D_123]: (r2_hidden(D_123, k1_xboole_0) | ~r2_hidden(D_123, '#skF_7') | ~r2_hidden(D_123, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_2])).
% 5.28/1.98  tff(c_239, plain, (![A_70, B_71]: (r2_hidden('#skF_3'(A_70, B_71), B_71) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.28/1.98  tff(c_72, plain, (r1_xboole_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.28/1.98  tff(c_106, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.28/1.98  tff(c_114, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_106])).
% 5.28/1.98  tff(c_214, plain, (![D_64, A_65, B_66]: (r2_hidden(D_64, A_65) | ~r2_hidden(D_64, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.28/1.98  tff(c_224, plain, (![D_64]: (r2_hidden(D_64, '#skF_8') | ~r2_hidden(D_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_114, c_214])).
% 5.28/1.98  tff(c_253, plain, (![A_70]: (r2_hidden('#skF_3'(A_70, k1_xboole_0), '#skF_8') | r1_xboole_0(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_239, c_224])).
% 5.28/1.98  tff(c_98, plain, (![B_43, A_44]: (r1_xboole_0(B_43, A_44) | ~r1_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.28/1.98  tff(c_101, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_98])).
% 5.28/1.98  tff(c_113, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_106])).
% 5.28/1.98  tff(c_221, plain, (![D_64]: (r2_hidden(D_64, '#skF_7') | ~r2_hidden(D_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_214])).
% 5.28/1.98  tff(c_252, plain, (![A_70]: (r2_hidden('#skF_3'(A_70, k1_xboole_0), '#skF_7') | r1_xboole_0(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_239, c_221])).
% 5.28/1.98  tff(c_362, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, B_93) | ~r2_hidden(C_94, A_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.28/1.98  tff(c_375, plain, (![C_95]: (~r2_hidden(C_95, '#skF_7') | ~r2_hidden(C_95, '#skF_8'))), inference(resolution, [status(thm)], [c_72, c_362])).
% 5.28/1.98  tff(c_571, plain, (![A_108]: (~r2_hidden('#skF_3'(A_108, k1_xboole_0), '#skF_8') | r1_xboole_0(A_108, k1_xboole_0))), inference(resolution, [status(thm)], [c_252, c_375])).
% 5.28/1.98  tff(c_591, plain, (![A_109]: (r1_xboole_0(A_109, k1_xboole_0))), inference(resolution, [status(thm)], [c_253, c_571])).
% 5.28/1.98  tff(c_26, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, B_12) | ~r2_hidden(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.28/1.98  tff(c_599, plain, (![C_15, A_109]: (~r2_hidden(C_15, k1_xboole_0) | ~r2_hidden(C_15, A_109))), inference(resolution, [status(thm)], [c_591, c_26])).
% 5.28/1.98  tff(c_953, plain, (![D_156, A_157]: (~r2_hidden(D_156, A_157) | ~r2_hidden(D_156, '#skF_7') | ~r2_hidden(D_156, '#skF_6'))), inference(resolution, [status(thm)], [c_724, c_599])).
% 5.28/1.98  tff(c_984, plain, (![A_158]: (~r2_hidden(A_158, '#skF_7') | ~r2_hidden(A_158, '#skF_6'))), inference(resolution, [status(thm)], [c_87, c_953])).
% 5.28/1.98  tff(c_1002, plain, (![A_159]: (~r2_hidden('#skF_3'(A_159, '#skF_7'), '#skF_6') | r1_xboole_0(A_159, '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_984])).
% 5.28/1.98  tff(c_1007, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_30, c_1002])).
% 5.28/1.98  tff(c_24, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.28/1.98  tff(c_1024, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1007, c_24])).
% 5.28/1.98  tff(c_512, plain, (![A_100, C_101, B_102]: (~r1_xboole_0(A_100, C_101) | ~r1_xboole_0(A_100, B_102) | r1_xboole_0(A_100, k2_xboole_0(B_102, C_101)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.28/1.98  tff(c_4049, plain, (![B_7790, C_7791, A_7792]: (r1_xboole_0(k2_xboole_0(B_7790, C_7791), A_7792) | ~r1_xboole_0(A_7792, C_7791) | ~r1_xboole_0(A_7792, B_7790))), inference(resolution, [status(thm)], [c_512, c_24])).
% 5.28/1.98  tff(c_70, plain, (~r1_xboole_0(k2_xboole_0('#skF_6', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.28/1.98  tff(c_4071, plain, (~r1_xboole_0('#skF_7', '#skF_8') | ~r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_4049, c_70])).
% 5.28/1.98  tff(c_4086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1024, c_101, c_4071])).
% 5.28/1.98  tff(c_4087, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_9')), inference(splitRight, [status(thm)], [c_357])).
% 5.28/1.98  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.28/1.98  tff(c_4152, plain, (![D_7852]: (r2_hidden(D_7852, '#skF_7') | ~r2_hidden(D_7852, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_4087, c_4])).
% 5.28/1.98  tff(c_4167, plain, (r2_hidden('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_87, c_4152])).
% 5.28/1.98  tff(c_374, plain, (![C_94]: (~r2_hidden(C_94, '#skF_7') | ~r2_hidden(C_94, '#skF_8'))), inference(resolution, [status(thm)], [c_72, c_362])).
% 5.28/1.98  tff(c_4192, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_4167, c_374])).
% 5.28/1.98  tff(c_4196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4192])).
% 5.28/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.28/1.98  
% 5.28/1.98  Inference rules
% 5.28/1.98  ----------------------
% 5.28/1.98  #Ref     : 0
% 5.28/1.98  #Sup     : 724
% 5.28/1.98  #Fact    : 4
% 5.28/1.98  #Define  : 0
% 5.28/1.98  #Split   : 9
% 5.28/1.98  #Chain   : 0
% 5.28/1.98  #Close   : 0
% 5.28/1.98  
% 5.28/1.98  Ordering : KBO
% 5.28/1.98  
% 5.28/1.98  Simplification rules
% 5.28/1.98  ----------------------
% 5.28/1.98  #Subsume      : 117
% 5.28/1.98  #Demod        : 154
% 5.28/1.98  #Tautology    : 220
% 5.28/1.98  #SimpNegUnit  : 14
% 5.28/1.98  #BackRed      : 3
% 5.28/1.98  
% 5.28/1.98  #Partial instantiations: 4420
% 5.28/1.98  #Strategies tried      : 1
% 5.28/1.98  
% 5.28/1.98  Timing (in seconds)
% 5.28/1.98  ----------------------
% 5.28/1.98  Preprocessing        : 0.34
% 5.28/1.98  Parsing              : 0.18
% 5.28/1.98  CNF conversion       : 0.03
% 5.28/1.98  Main loop            : 0.88
% 5.28/1.98  Inferencing          : 0.39
% 5.28/1.98  Reduction            : 0.24
% 5.28/1.98  Demodulation         : 0.16
% 5.28/1.98  BG Simplification    : 0.04
% 5.28/1.98  Subsumption          : 0.15
% 5.28/1.98  Abstraction          : 0.04
% 5.28/1.98  MUC search           : 0.00
% 5.28/1.98  Cooper               : 0.00
% 5.28/1.98  Total                : 1.26
% 5.28/1.98  Index Insertion      : 0.00
% 5.28/1.98  Index Deletion       : 0.00
% 5.28/1.98  Index Matching       : 0.00
% 5.28/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
