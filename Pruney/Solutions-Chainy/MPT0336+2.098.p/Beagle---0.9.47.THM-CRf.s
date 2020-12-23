%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:13 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 115 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 227 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_80,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_163,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [E_25,B_20,C_21] : r2_hidden(E_25,k1_enumset1(E_25,B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_181,plain,(
    ! [A_59,B_60] : r2_hidden(A_59,k2_tarski(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_184,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_181])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_241,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_3'(A_77,B_78),A_77)
      | r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_94,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_94])).

tff(c_105,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_105])).

tff(c_232,plain,(
    ! [D_72,B_73,A_74] :
      ( r2_hidden(D_72,B_73)
      | ~ r2_hidden(D_72,k3_xboole_0(A_74,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_235,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,'#skF_8')
      | ~ r2_hidden(D_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_232])).

tff(c_254,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_78),'#skF_8')
      | r1_xboole_0(k1_xboole_0,B_78) ) ),
    inference(resolution,[status(thm)],[c_241,c_235])).

tff(c_269,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_3'(A_82,B_83),B_83)
      | r1_xboole_0(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_105])).

tff(c_238,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,'#skF_7')
      | ~ r2_hidden(D_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_232])).

tff(c_356,plain,(
    ! [A_95] :
      ( r2_hidden('#skF_3'(A_95,k1_xboole_0),'#skF_7')
      | r1_xboole_0(A_95,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_269,c_238])).

tff(c_299,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_311,plain,(
    ! [C_88] :
      ( ~ r2_hidden(C_88,'#skF_7')
      | ~ r2_hidden(C_88,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_78,c_299])).

tff(c_492,plain,(
    ! [A_104] :
      ( ~ r2_hidden('#skF_3'(A_104,k1_xboole_0),'#skF_8')
      | r1_xboole_0(A_104,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_356,c_311])).

tff(c_501,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_254,c_492])).

tff(c_26,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_510,plain,(
    ! [C_15] : ~ r2_hidden(C_15,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_501,c_26])).

tff(c_82,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_7'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_367,plain,(
    ! [B_97,A_98] :
      ( k1_tarski(B_97) = A_98
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,k1_tarski(B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_377,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_9')
    | k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_367])).

tff(c_416,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_714,plain,(
    ! [D_113,A_114,B_115] :
      ( r2_hidden(D_113,k3_xboole_0(A_114,B_115))
      | ~ r2_hidden(D_113,B_115)
      | ~ r2_hidden(D_113,A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_732,plain,(
    ! [D_113] :
      ( r2_hidden(D_113,k1_xboole_0)
      | ~ r2_hidden(D_113,'#skF_7')
      | ~ r2_hidden(D_113,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_714])).

tff(c_748,plain,(
    ! [D_116] :
      ( ~ r2_hidden(D_116,'#skF_7')
      | ~ r2_hidden(D_116,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_732])).

tff(c_759,plain,(
    ! [B_117] :
      ( ~ r2_hidden('#skF_3'('#skF_7',B_117),'#skF_6')
      | r1_xboole_0('#skF_7',B_117) ) ),
    inference(resolution,[status(thm)],[c_30,c_748])).

tff(c_764,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_759])).

tff(c_562,plain,(
    ! [A_107,C_108,B_109] :
      ( ~ r1_xboole_0(A_107,C_108)
      | ~ r1_xboole_0(A_107,B_109)
      | r1_xboole_0(A_107,k2_xboole_0(B_109,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4689,plain,(
    ! [B_9600,C_9601,A_9602] :
      ( r1_xboole_0(k2_xboole_0(B_9600,C_9601),A_9602)
      | ~ r1_xboole_0(A_9602,C_9601)
      | ~ r1_xboole_0(A_9602,B_9600) ) ),
    inference(resolution,[status(thm)],[c_562,c_24])).

tff(c_76,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_6','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4711,plain,
    ( ~ r1_xboole_0('#skF_7','#skF_8')
    | ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_4689,c_76])).

tff(c_4726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_97,c_4711])).

tff(c_4727,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_9') ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4991,plain,(
    ! [D_9684] :
      ( r2_hidden(D_9684,'#skF_7')
      | ~ r2_hidden(D_9684,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4727,c_4])).

tff(c_5006,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_184,c_4991])).

tff(c_5009,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_5006,c_311])).

tff(c_5013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:38:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.20  
% 5.94/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5
% 5.94/2.20  
% 5.94/2.20  %Foreground sorts:
% 5.94/2.20  
% 5.94/2.20  
% 5.94/2.20  %Background operators:
% 5.94/2.20  
% 5.94/2.20  
% 5.94/2.20  %Foreground operators:
% 5.94/2.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.94/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.94/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.20  tff('#skF_7', type, '#skF_7': $i).
% 5.94/2.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.94/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.94/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.94/2.20  tff('#skF_6', type, '#skF_6': $i).
% 5.94/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.94/2.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.94/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.94/2.20  tff('#skF_9', type, '#skF_9': $i).
% 5.94/2.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.94/2.20  tff('#skF_8', type, '#skF_8': $i).
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.94/2.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.94/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.94/2.20  
% 5.94/2.22  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.94/2.22  tff(f_93, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.94/2.22  tff(f_95, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.94/2.22  tff(f_91, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.94/2.22  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.94/2.22  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.94/2.22  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.94/2.22  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.94/2.22  tff(f_103, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.94/2.22  tff(f_76, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.94/2.22  tff(c_80, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.94/2.22  tff(c_62, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.94/2.22  tff(c_163, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.94/2.22  tff(c_44, plain, (![E_25, B_20, C_21]: (r2_hidden(E_25, k1_enumset1(E_25, B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.94/2.22  tff(c_181, plain, (![A_59, B_60]: (r2_hidden(A_59, k2_tarski(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_44])).
% 5.94/2.22  tff(c_184, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_181])).
% 5.94/2.22  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.94/2.22  tff(c_30, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.94/2.22  tff(c_241, plain, (![A_77, B_78]: (r2_hidden('#skF_3'(A_77, B_78), A_77) | r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.94/2.22  tff(c_78, plain, (r1_xboole_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.94/2.22  tff(c_94, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.94/2.22  tff(c_97, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_78, c_94])).
% 5.94/2.22  tff(c_105, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.94/2.22  tff(c_112, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_97, c_105])).
% 5.94/2.22  tff(c_232, plain, (![D_72, B_73, A_74]: (r2_hidden(D_72, B_73) | ~r2_hidden(D_72, k3_xboole_0(A_74, B_73)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.94/2.22  tff(c_235, plain, (![D_72]: (r2_hidden(D_72, '#skF_8') | ~r2_hidden(D_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_112, c_232])).
% 5.94/2.22  tff(c_254, plain, (![B_78]: (r2_hidden('#skF_3'(k1_xboole_0, B_78), '#skF_8') | r1_xboole_0(k1_xboole_0, B_78))), inference(resolution, [status(thm)], [c_241, c_235])).
% 5.94/2.22  tff(c_269, plain, (![A_82, B_83]: (r2_hidden('#skF_3'(A_82, B_83), B_83) | r1_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.94/2.22  tff(c_113, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_105])).
% 5.94/2.22  tff(c_238, plain, (![D_72]: (r2_hidden(D_72, '#skF_7') | ~r2_hidden(D_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_232])).
% 5.94/2.22  tff(c_356, plain, (![A_95]: (r2_hidden('#skF_3'(A_95, k1_xboole_0), '#skF_7') | r1_xboole_0(A_95, k1_xboole_0))), inference(resolution, [status(thm)], [c_269, c_238])).
% 5.94/2.22  tff(c_299, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.94/2.22  tff(c_311, plain, (![C_88]: (~r2_hidden(C_88, '#skF_7') | ~r2_hidden(C_88, '#skF_8'))), inference(resolution, [status(thm)], [c_78, c_299])).
% 5.94/2.22  tff(c_492, plain, (![A_104]: (~r2_hidden('#skF_3'(A_104, k1_xboole_0), '#skF_8') | r1_xboole_0(A_104, k1_xboole_0))), inference(resolution, [status(thm)], [c_356, c_311])).
% 5.94/2.22  tff(c_501, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_254, c_492])).
% 5.94/2.22  tff(c_26, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, B_12) | ~r2_hidden(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.94/2.22  tff(c_510, plain, (![C_15]: (~r2_hidden(C_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_501, c_26])).
% 5.94/2.22  tff(c_82, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.94/2.22  tff(c_367, plain, (![B_97, A_98]: (k1_tarski(B_97)=A_98 | k1_xboole_0=A_98 | ~r1_tarski(A_98, k1_tarski(B_97)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.22  tff(c_377, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_9') | k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_367])).
% 5.94/2.22  tff(c_416, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_377])).
% 5.94/2.22  tff(c_714, plain, (![D_113, A_114, B_115]: (r2_hidden(D_113, k3_xboole_0(A_114, B_115)) | ~r2_hidden(D_113, B_115) | ~r2_hidden(D_113, A_114))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.94/2.22  tff(c_732, plain, (![D_113]: (r2_hidden(D_113, k1_xboole_0) | ~r2_hidden(D_113, '#skF_7') | ~r2_hidden(D_113, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_416, c_714])).
% 5.94/2.22  tff(c_748, plain, (![D_116]: (~r2_hidden(D_116, '#skF_7') | ~r2_hidden(D_116, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_510, c_732])).
% 5.94/2.22  tff(c_759, plain, (![B_117]: (~r2_hidden('#skF_3'('#skF_7', B_117), '#skF_6') | r1_xboole_0('#skF_7', B_117))), inference(resolution, [status(thm)], [c_30, c_748])).
% 5.94/2.22  tff(c_764, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_28, c_759])).
% 5.94/2.22  tff(c_562, plain, (![A_107, C_108, B_109]: (~r1_xboole_0(A_107, C_108) | ~r1_xboole_0(A_107, B_109) | r1_xboole_0(A_107, k2_xboole_0(B_109, C_108)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.94/2.22  tff(c_24, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.94/2.22  tff(c_4689, plain, (![B_9600, C_9601, A_9602]: (r1_xboole_0(k2_xboole_0(B_9600, C_9601), A_9602) | ~r1_xboole_0(A_9602, C_9601) | ~r1_xboole_0(A_9602, B_9600))), inference(resolution, [status(thm)], [c_562, c_24])).
% 5.94/2.22  tff(c_76, plain, (~r1_xboole_0(k2_xboole_0('#skF_6', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.94/2.22  tff(c_4711, plain, (~r1_xboole_0('#skF_7', '#skF_8') | ~r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_4689, c_76])).
% 5.94/2.22  tff(c_4726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_764, c_97, c_4711])).
% 5.94/2.22  tff(c_4727, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_9')), inference(splitRight, [status(thm)], [c_377])).
% 5.94/2.22  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.94/2.22  tff(c_4991, plain, (![D_9684]: (r2_hidden(D_9684, '#skF_7') | ~r2_hidden(D_9684, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_4727, c_4])).
% 5.94/2.22  tff(c_5006, plain, (r2_hidden('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_184, c_4991])).
% 5.94/2.22  tff(c_5009, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_5006, c_311])).
% 5.94/2.22  tff(c_5013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_5009])).
% 5.94/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.22  
% 5.94/2.22  Inference rules
% 5.94/2.22  ----------------------
% 5.94/2.22  #Ref     : 0
% 5.94/2.22  #Sup     : 905
% 5.94/2.22  #Fact    : 12
% 5.94/2.22  #Define  : 0
% 5.94/2.22  #Split   : 9
% 5.94/2.22  #Chain   : 0
% 5.94/2.22  #Close   : 0
% 5.94/2.22  
% 5.94/2.22  Ordering : KBO
% 5.94/2.22  
% 5.94/2.22  Simplification rules
% 5.94/2.22  ----------------------
% 5.94/2.22  #Subsume      : 197
% 5.94/2.22  #Demod        : 185
% 5.94/2.22  #Tautology    : 271
% 5.94/2.22  #SimpNegUnit  : 29
% 5.94/2.22  #BackRed      : 3
% 5.94/2.22  
% 5.94/2.22  #Partial instantiations: 5100
% 5.94/2.22  #Strategies tried      : 1
% 5.94/2.22  
% 5.94/2.22  Timing (in seconds)
% 5.94/2.22  ----------------------
% 5.94/2.22  Preprocessing        : 0.36
% 5.94/2.22  Parsing              : 0.18
% 5.94/2.22  CNF conversion       : 0.03
% 5.94/2.22  Main loop            : 1.09
% 5.94/2.22  Inferencing          : 0.49
% 5.94/2.22  Reduction            : 0.28
% 5.94/2.22  Demodulation         : 0.19
% 5.94/2.22  BG Simplification    : 0.05
% 5.94/2.22  Subsumption          : 0.19
% 5.94/2.22  Abstraction          : 0.06
% 5.94/2.22  MUC search           : 0.00
% 5.94/2.22  Cooper               : 0.00
% 5.94/2.22  Total                : 1.48
% 5.94/2.22  Index Insertion      : 0.00
% 5.94/2.22  Index Deletion       : 0.00
% 5.94/2.22  Index Matching       : 0.00
% 5.94/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
