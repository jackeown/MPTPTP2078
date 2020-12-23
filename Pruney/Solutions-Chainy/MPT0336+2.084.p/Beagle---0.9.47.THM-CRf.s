%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 12.47s
% Output     : CNFRefutation 12.61s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 159 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 223 expanded)
%              Number of equality atoms :   31 (  79 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_22,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = A_52
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_174,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(resolution,[status(thm)],[c_22,c_150])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_98,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_98])).

tff(c_172,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_103,c_150])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1165,plain,(
    ! [A_102,C_103,B_104] :
      ( r1_xboole_0(A_102,C_103)
      | ~ r1_tarski(A_102,k4_xboole_0(B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1772,plain,(
    ! [B_127,C_128,B_129] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_127,C_128),B_129),C_128) ),
    inference(resolution,[status(thm)],[c_18,c_1165])).

tff(c_1926,plain,(
    ! [B_134] : r1_xboole_0(k4_xboole_0('#skF_3',B_134),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_1772])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18644,plain,(
    ! [B_452] : k4_xboole_0(k4_xboole_0('#skF_3',B_452),'#skF_4') = k4_xboole_0('#skF_3',B_452) ),
    inference(resolution,[status(thm)],[c_1926,c_30])).

tff(c_18802,plain,(
    ! [B_18] : k4_xboole_0(k3_xboole_0('#skF_3',B_18),'#skF_4') = k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_18644])).

tff(c_18858,plain,(
    ! [B_18] : k4_xboole_0(k3_xboole_0('#skF_3',B_18),'#skF_4') = k3_xboole_0('#skF_3',B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18802])).

tff(c_498,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k4_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    ! [A_19] : r1_xboole_0(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_171,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_150])).

tff(c_557,plain,(
    ! [B_78] : k3_xboole_0(k1_xboole_0,B_78) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_171])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_578,plain,(
    ! [B_78] : k3_xboole_0(B_78,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_2])).

tff(c_540,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_498])).

tff(c_819,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_540])).

tff(c_718,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,k1_tarski(B_83)) = A_82
      | r2_hidden(B_83,A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_724,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,A_82) = k3_xboole_0(A_82,k1_tarski(B_83))
      | r2_hidden(B_83,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_20])).

tff(c_6449,plain,(
    ! [A_229,B_230] :
      ( k3_xboole_0(A_229,k1_tarski(B_230)) = k1_xboole_0
      | r2_hidden(B_230,A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_724])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_133,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_140,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_133])).

tff(c_6573,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6449,c_140])).

tff(c_8934,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6573])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2162,plain,(
    ! [A_141,B_142,C_143] :
      ( ~ r1_xboole_0(A_141,B_142)
      | ~ r2_hidden(C_143,B_142)
      | ~ r2_hidden(C_143,A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9715,plain,(
    ! [C_318,B_319,A_320] :
      ( ~ r2_hidden(C_318,B_319)
      | ~ r2_hidden(C_318,A_320)
      | k4_xboole_0(A_320,B_319) != A_320 ) ),
    inference(resolution,[status(thm)],[c_32,c_2162])).

tff(c_9731,plain,(
    ! [A_321] :
      ( ~ r2_hidden('#skF_5',A_321)
      | k4_xboole_0(A_321,'#skF_4') != A_321 ) ),
    inference(resolution,[status(thm)],[c_50,c_9715])).

tff(c_9743,plain,(
    k4_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_8934,c_9731])).

tff(c_32680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18858,c_9743])).

tff(c_32681,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6573])).

tff(c_114,plain,(
    ! [A_44,B_45] : r1_xboole_0(k4_xboole_0(A_44,k3_xboole_0(A_44,B_45)),B_45) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_399,plain,(
    ! [B_65,A_66] : r1_xboole_0(k4_xboole_0(B_65,k3_xboole_0(A_66,B_65)),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_421,plain,(
    ! [A_66,B_65] : r1_xboole_0(A_66,k4_xboole_0(B_65,k3_xboole_0(A_66,B_65))) ),
    inference(resolution,[status(thm)],[c_399,c_4])).

tff(c_32754,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_2',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32681,c_421])).

tff(c_32779,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_32754])).

tff(c_2779,plain,(
    ! [A_156,C_157,B_158] :
      ( ~ r1_xboole_0(A_156,C_157)
      | ~ r1_xboole_0(A_156,B_158)
      | r1_xboole_0(A_156,k2_xboole_0(B_158,C_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_33786,plain,(
    ! [B_571,C_572,A_573] :
      ( r1_xboole_0(k2_xboole_0(B_571,C_572),A_573)
      | ~ r1_xboole_0(A_573,C_572)
      | ~ r1_xboole_0(A_573,B_571) ) ),
    inference(resolution,[status(thm)],[c_2779,c_4])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_33804,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_33786,c_46])).

tff(c_33813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32779,c_103,c_33804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.47/4.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.47/4.89  
% 12.47/4.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.47/4.89  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.47/4.89  
% 12.47/4.89  %Foreground sorts:
% 12.47/4.89  
% 12.47/4.89  
% 12.47/4.89  %Background operators:
% 12.47/4.89  
% 12.47/4.89  
% 12.47/4.89  %Foreground operators:
% 12.47/4.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.47/4.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.47/4.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.47/4.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.47/4.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.47/4.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.47/4.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.47/4.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.47/4.89  tff('#skF_5', type, '#skF_5': $i).
% 12.47/4.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.47/4.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.47/4.89  tff('#skF_2', type, '#skF_2': $i).
% 12.47/4.89  tff('#skF_3', type, '#skF_3': $i).
% 12.47/4.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.47/4.89  tff('#skF_4', type, '#skF_4': $i).
% 12.47/4.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.47/4.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.47/4.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.47/4.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.47/4.89  
% 12.61/4.91  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.61/4.91  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.61/4.91  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.61/4.91  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 12.61/4.91  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.61/4.91  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.61/4.91  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 12.61/4.91  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.61/4.91  tff(f_98, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 12.61/4.91  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.61/4.91  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 12.61/4.91  tff(f_87, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 12.61/4.91  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 12.61/4.91  tff(c_22, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.61/4.91  tff(c_150, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=A_52 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.61/4.91  tff(c_174, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(resolution, [status(thm)], [c_22, c_150])).
% 12.61/4.91  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.61/4.91  tff(c_48, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.61/4.91  tff(c_98, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.61/4.91  tff(c_103, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_98])).
% 12.61/4.91  tff(c_172, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_103, c_150])).
% 12.61/4.91  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.61/4.91  tff(c_1165, plain, (![A_102, C_103, B_104]: (r1_xboole_0(A_102, C_103) | ~r1_tarski(A_102, k4_xboole_0(B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.61/4.91  tff(c_1772, plain, (![B_127, C_128, B_129]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_127, C_128), B_129), C_128))), inference(resolution, [status(thm)], [c_18, c_1165])).
% 12.61/4.91  tff(c_1926, plain, (![B_134]: (r1_xboole_0(k4_xboole_0('#skF_3', B_134), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_1772])).
% 12.61/4.91  tff(c_30, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.61/4.91  tff(c_18644, plain, (![B_452]: (k4_xboole_0(k4_xboole_0('#skF_3', B_452), '#skF_4')=k4_xboole_0('#skF_3', B_452))), inference(resolution, [status(thm)], [c_1926, c_30])).
% 12.61/4.91  tff(c_18802, plain, (![B_18]: (k4_xboole_0(k3_xboole_0('#skF_3', B_18), '#skF_4')=k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', B_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_18644])).
% 12.61/4.91  tff(c_18858, plain, (![B_18]: (k4_xboole_0(k3_xboole_0('#skF_3', B_18), '#skF_4')=k3_xboole_0('#skF_3', B_18))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18802])).
% 12.61/4.91  tff(c_498, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k4_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.61/4.91  tff(c_104, plain, (![A_19]: (r1_xboole_0(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_22, c_98])).
% 12.61/4.91  tff(c_171, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_150])).
% 12.61/4.91  tff(c_557, plain, (![B_78]: (k3_xboole_0(k1_xboole_0, B_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_498, c_171])).
% 12.61/4.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.61/4.91  tff(c_578, plain, (![B_78]: (k3_xboole_0(B_78, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_557, c_2])).
% 12.61/4.91  tff(c_540, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_174, c_498])).
% 12.61/4.91  tff(c_819, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_578, c_540])).
% 12.61/4.91  tff(c_718, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k1_tarski(B_83))=A_82 | r2_hidden(B_83, A_82))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.61/4.91  tff(c_724, plain, (![A_82, B_83]: (k4_xboole_0(A_82, A_82)=k3_xboole_0(A_82, k1_tarski(B_83)) | r2_hidden(B_83, A_82))), inference(superposition, [status(thm), theory('equality')], [c_718, c_20])).
% 12.61/4.91  tff(c_6449, plain, (![A_229, B_230]: (k3_xboole_0(A_229, k1_tarski(B_230))=k1_xboole_0 | r2_hidden(B_230, A_229))), inference(demodulation, [status(thm), theory('equality')], [c_819, c_724])).
% 12.61/4.91  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.61/4.91  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 12.61/4.91  tff(c_133, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.61/4.91  tff(c_140, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_133])).
% 12.61/4.91  tff(c_6573, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6449, c_140])).
% 12.61/4.91  tff(c_8934, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6573])).
% 12.61/4.91  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.61/4.91  tff(c_32, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.61/4.91  tff(c_2162, plain, (![A_141, B_142, C_143]: (~r1_xboole_0(A_141, B_142) | ~r2_hidden(C_143, B_142) | ~r2_hidden(C_143, A_141))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.61/4.91  tff(c_9715, plain, (![C_318, B_319, A_320]: (~r2_hidden(C_318, B_319) | ~r2_hidden(C_318, A_320) | k4_xboole_0(A_320, B_319)!=A_320)), inference(resolution, [status(thm)], [c_32, c_2162])).
% 12.61/4.91  tff(c_9731, plain, (![A_321]: (~r2_hidden('#skF_5', A_321) | k4_xboole_0(A_321, '#skF_4')!=A_321)), inference(resolution, [status(thm)], [c_50, c_9715])).
% 12.61/4.91  tff(c_9743, plain, (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_8934, c_9731])).
% 12.61/4.91  tff(c_32680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18858, c_9743])).
% 12.61/4.91  tff(c_32681, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6573])).
% 12.61/4.91  tff(c_114, plain, (![A_44, B_45]: (r1_xboole_0(k4_xboole_0(A_44, k3_xboole_0(A_44, B_45)), B_45))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.61/4.91  tff(c_399, plain, (![B_65, A_66]: (r1_xboole_0(k4_xboole_0(B_65, k3_xboole_0(A_66, B_65)), A_66))), inference(superposition, [status(thm), theory('equality')], [c_2, c_114])).
% 12.61/4.91  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.61/4.91  tff(c_421, plain, (![A_66, B_65]: (r1_xboole_0(A_66, k4_xboole_0(B_65, k3_xboole_0(A_66, B_65))))), inference(resolution, [status(thm)], [c_399, c_4])).
% 12.61/4.91  tff(c_32754, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_2', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32681, c_421])).
% 12.61/4.91  tff(c_32779, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_32754])).
% 12.61/4.91  tff(c_2779, plain, (![A_156, C_157, B_158]: (~r1_xboole_0(A_156, C_157) | ~r1_xboole_0(A_156, B_158) | r1_xboole_0(A_156, k2_xboole_0(B_158, C_157)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.61/4.91  tff(c_33786, plain, (![B_571, C_572, A_573]: (r1_xboole_0(k2_xboole_0(B_571, C_572), A_573) | ~r1_xboole_0(A_573, C_572) | ~r1_xboole_0(A_573, B_571))), inference(resolution, [status(thm)], [c_2779, c_4])).
% 12.61/4.91  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.61/4.91  tff(c_33804, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_33786, c_46])).
% 12.61/4.91  tff(c_33813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32779, c_103, c_33804])).
% 12.61/4.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.61/4.91  
% 12.61/4.91  Inference rules
% 12.61/4.91  ----------------------
% 12.61/4.91  #Ref     : 0
% 12.61/4.91  #Sup     : 8162
% 12.61/4.91  #Fact    : 0
% 12.61/4.91  #Define  : 0
% 12.61/4.91  #Split   : 6
% 12.61/4.91  #Chain   : 0
% 12.61/4.91  #Close   : 0
% 12.61/4.91  
% 12.61/4.91  Ordering : KBO
% 12.61/4.91  
% 12.61/4.91  Simplification rules
% 12.61/4.91  ----------------------
% 12.61/4.91  #Subsume      : 404
% 12.61/4.91  #Demod        : 8163
% 12.61/4.91  #Tautology    : 6289
% 12.61/4.91  #SimpNegUnit  : 27
% 12.61/4.91  #BackRed      : 28
% 12.61/4.91  
% 12.61/4.91  #Partial instantiations: 0
% 12.61/4.91  #Strategies tried      : 1
% 12.61/4.91  
% 12.61/4.91  Timing (in seconds)
% 12.61/4.91  ----------------------
% 12.61/4.91  Preprocessing        : 0.33
% 12.61/4.91  Parsing              : 0.18
% 12.61/4.91  CNF conversion       : 0.02
% 12.61/4.91  Main loop            : 3.81
% 12.61/4.91  Inferencing          : 0.71
% 12.61/4.91  Reduction            : 2.08
% 12.61/4.91  Demodulation         : 1.76
% 12.61/4.91  BG Simplification    : 0.07
% 12.61/4.91  Subsumption          : 0.74
% 12.61/4.91  Abstraction          : 0.10
% 12.61/4.91  MUC search           : 0.00
% 12.61/4.91  Cooper               : 0.00
% 12.61/4.91  Total                : 4.18
% 12.61/4.91  Index Insertion      : 0.00
% 12.61/4.91  Index Deletion       : 0.00
% 12.61/4.91  Index Matching       : 0.00
% 12.61/4.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
