%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:04 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 215 expanded)
%              Number of leaves         :   29 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 371 expanded)
%              Number of equality atoms :   32 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_105,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

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

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_95,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_443,plain,(
    ! [A_87,C_88,B_89] :
      ( ~ r1_xboole_0(A_87,C_88)
      | ~ r1_xboole_0(A_87,B_89)
      | r1_xboole_0(A_87,k2_xboole_0(B_89,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3458,plain,(
    ! [B_224,C_225,A_226] :
      ( r1_xboole_0(k2_xboole_0(B_224,C_225),A_226)
      | ~ r1_xboole_0(A_226,C_225)
      | ~ r1_xboole_0(A_226,B_224) ) ),
    inference(resolution,[status(thm)],[c_443,c_4])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3478,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3458,c_42])).

tff(c_3487,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3478])).

tff(c_3499,plain,(
    k4_xboole_0('#skF_3','#skF_2') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_3487])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_119,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_107])).

tff(c_118,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_98,c_107])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_218,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_206])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(k1_tarski(A_30),B_31)
      | r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_406,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_xboole_0(A_83,C_84)
      | ~ r1_xboole_0(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2970,plain,(
    ! [A_200,B_201,A_202] :
      ( r1_xboole_0(A_200,B_201)
      | ~ r1_tarski(A_200,k1_tarski(A_202))
      | r2_hidden(A_202,B_201) ) ),
    inference(resolution,[status(thm)],[c_40,c_406])).

tff(c_2990,plain,(
    ! [B_203] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_203)
      | r2_hidden('#skF_5',B_203) ) ),
    inference(resolution,[status(thm)],[c_50,c_2970])).

tff(c_3014,plain,(
    ! [B_204] :
      ( r1_xboole_0(B_204,k3_xboole_0('#skF_3','#skF_2'))
      | r2_hidden('#skF_5',B_204) ) ),
    inference(resolution,[status(thm)],[c_2990,c_4])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18483,plain,(
    ! [B_624] :
      ( k4_xboole_0(B_624,k3_xboole_0('#skF_3','#skF_2')) = B_624
      | r2_hidden('#skF_5',B_624) ) ),
    inference(resolution,[status(thm)],[c_3014,c_30])).

tff(c_489,plain,(
    ! [A_91] :
      ( r1_xboole_0(A_91,'#skF_4')
      | ~ r1_tarski(A_91,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_98,c_406])).

tff(c_549,plain,(
    ! [A_94] :
      ( k4_xboole_0(A_94,'#skF_4') = A_94
      | ~ r1_tarski(A_94,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_489,c_30])).

tff(c_568,plain,(
    ! [B_13] : k4_xboole_0(k4_xboole_0('#skF_3',B_13),'#skF_4') = k4_xboole_0('#skF_3',B_13) ),
    inference(resolution,[status(thm)],[c_18,c_549])).

tff(c_18790,plain,
    ( k4_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18483,c_568])).

tff(c_18922,plain,
    ( k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_218,c_18790])).

tff(c_20924,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18922])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_145,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_155,plain,(
    ! [B_47,A_46] :
      ( r1_xboole_0(B_47,A_46)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(resolution,[status(thm)],[c_145,c_4])).

tff(c_331,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,B_75)
      | ~ r2_hidden(C_76,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6489,plain,(
    ! [C_343,A_344,B_345] :
      ( ~ r2_hidden(C_343,A_344)
      | ~ r2_hidden(C_343,B_345)
      | k4_xboole_0(A_344,B_345) != A_344 ) ),
    inference(resolution,[status(thm)],[c_155,c_331])).

tff(c_6510,plain,(
    ! [B_345] :
      ( ~ r2_hidden('#skF_5',B_345)
      | k4_xboole_0('#skF_4',B_345) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_46,c_6489])).

tff(c_20937,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_20924,c_6510])).

tff(c_20963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_20937])).

tff(c_20964,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18922])).

tff(c_177,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1768,plain,(
    ! [A_152,B_153] :
      ( k4_xboole_0(A_152,B_153) = A_152
      | ~ r1_tarski(A_152,k4_xboole_0(A_152,B_153)) ) ),
    inference(resolution,[status(thm)],[c_18,c_177])).

tff(c_1822,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = A_14
      | ~ r1_tarski(A_14,k3_xboole_0(A_14,B_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1768])).

tff(c_4108,plain,(
    ! [A_257,B_258] :
      ( k3_xboole_0(A_257,B_258) = A_257
      | ~ r1_tarski(A_257,k3_xboole_0(A_257,B_258)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1822])).

tff(c_4130,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(B_2,A_1) = B_2
      | ~ r1_tarski(B_2,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4108])).

tff(c_21034,plain,
    ( k3_xboole_0(k4_xboole_0('#skF_3','#skF_2'),'#skF_3') = k4_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20964,c_4130])).

tff(c_21153,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20964,c_2,c_21034])).

tff(c_21155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3499,c_21153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.38/4.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.38/4.45  
% 11.38/4.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.38/4.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.38/4.45  
% 11.38/4.45  %Foreground sorts:
% 11.38/4.45  
% 11.38/4.45  
% 11.38/4.45  %Background operators:
% 11.38/4.45  
% 11.38/4.45  
% 11.38/4.45  %Foreground operators:
% 11.38/4.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.38/4.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.38/4.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.38/4.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.38/4.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.38/4.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.38/4.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.38/4.45  tff('#skF_5', type, '#skF_5': $i).
% 11.38/4.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.38/4.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.38/4.45  tff('#skF_2', type, '#skF_2': $i).
% 11.38/4.45  tff('#skF_3', type, '#skF_3': $i).
% 11.38/4.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.38/4.45  tff('#skF_4', type, '#skF_4': $i).
% 11.38/4.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.38/4.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.38/4.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.38/4.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.38/4.45  
% 11.49/4.47  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.49/4.47  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 11.49/4.47  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.49/4.47  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 11.49/4.47  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.49/4.47  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.49/4.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.49/4.47  tff(f_96, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 11.49/4.47  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.49/4.47  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.49/4.47  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.49/4.47  tff(c_32, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.49/4.47  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.49/4.47  tff(c_95, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.49/4.47  tff(c_98, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_95])).
% 11.49/4.47  tff(c_443, plain, (![A_87, C_88, B_89]: (~r1_xboole_0(A_87, C_88) | ~r1_xboole_0(A_87, B_89) | r1_xboole_0(A_87, k2_xboole_0(B_89, C_88)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.49/4.47  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.49/4.47  tff(c_3458, plain, (![B_224, C_225, A_226]: (r1_xboole_0(k2_xboole_0(B_224, C_225), A_226) | ~r1_xboole_0(A_226, C_225) | ~r1_xboole_0(A_226, B_224))), inference(resolution, [status(thm)], [c_443, c_4])).
% 11.49/4.47  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.49/4.47  tff(c_3478, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3458, c_42])).
% 11.49/4.47  tff(c_3487, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3478])).
% 11.49/4.47  tff(c_3499, plain, (k4_xboole_0('#skF_3', '#skF_2')!='#skF_3'), inference(resolution, [status(thm)], [c_32, c_3487])).
% 11.49/4.47  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.49/4.47  tff(c_107, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.49/4.47  tff(c_119, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_107])).
% 11.49/4.47  tff(c_118, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_98, c_107])).
% 11.49/4.47  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.49/4.47  tff(c_206, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.49/4.47  tff(c_218, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_206])).
% 11.49/4.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.49/4.47  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.49/4.47  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 11.49/4.47  tff(c_40, plain, (![A_30, B_31]: (r1_xboole_0(k1_tarski(A_30), B_31) | r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.49/4.47  tff(c_406, plain, (![A_83, C_84, B_85]: (r1_xboole_0(A_83, C_84) | ~r1_xboole_0(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.49/4.47  tff(c_2970, plain, (![A_200, B_201, A_202]: (r1_xboole_0(A_200, B_201) | ~r1_tarski(A_200, k1_tarski(A_202)) | r2_hidden(A_202, B_201))), inference(resolution, [status(thm)], [c_40, c_406])).
% 11.49/4.47  tff(c_2990, plain, (![B_203]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_203) | r2_hidden('#skF_5', B_203))), inference(resolution, [status(thm)], [c_50, c_2970])).
% 11.49/4.47  tff(c_3014, plain, (![B_204]: (r1_xboole_0(B_204, k3_xboole_0('#skF_3', '#skF_2')) | r2_hidden('#skF_5', B_204))), inference(resolution, [status(thm)], [c_2990, c_4])).
% 11.49/4.47  tff(c_30, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.49/4.47  tff(c_18483, plain, (![B_624]: (k4_xboole_0(B_624, k3_xboole_0('#skF_3', '#skF_2'))=B_624 | r2_hidden('#skF_5', B_624))), inference(resolution, [status(thm)], [c_3014, c_30])).
% 11.49/4.47  tff(c_489, plain, (![A_91]: (r1_xboole_0(A_91, '#skF_4') | ~r1_tarski(A_91, '#skF_3'))), inference(resolution, [status(thm)], [c_98, c_406])).
% 11.49/4.47  tff(c_549, plain, (![A_94]: (k4_xboole_0(A_94, '#skF_4')=A_94 | ~r1_tarski(A_94, '#skF_3'))), inference(resolution, [status(thm)], [c_489, c_30])).
% 11.49/4.47  tff(c_568, plain, (![B_13]: (k4_xboole_0(k4_xboole_0('#skF_3', B_13), '#skF_4')=k4_xboole_0('#skF_3', B_13))), inference(resolution, [status(thm)], [c_18, c_549])).
% 11.49/4.47  tff(c_18790, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18483, c_568])).
% 11.49/4.47  tff(c_18922, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_218, c_18790])).
% 11.49/4.47  tff(c_20924, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_18922])).
% 11.49/4.47  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.49/4.47  tff(c_145, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k4_xboole_0(A_46, B_47)!=A_46)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.49/4.47  tff(c_155, plain, (![B_47, A_46]: (r1_xboole_0(B_47, A_46) | k4_xboole_0(A_46, B_47)!=A_46)), inference(resolution, [status(thm)], [c_145, c_4])).
% 11.49/4.47  tff(c_331, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, B_75) | ~r2_hidden(C_76, A_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.49/4.47  tff(c_6489, plain, (![C_343, A_344, B_345]: (~r2_hidden(C_343, A_344) | ~r2_hidden(C_343, B_345) | k4_xboole_0(A_344, B_345)!=A_344)), inference(resolution, [status(thm)], [c_155, c_331])).
% 11.49/4.47  tff(c_6510, plain, (![B_345]: (~r2_hidden('#skF_5', B_345) | k4_xboole_0('#skF_4', B_345)!='#skF_4')), inference(resolution, [status(thm)], [c_46, c_6489])).
% 11.49/4.47  tff(c_20937, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_20924, c_6510])).
% 11.49/4.47  tff(c_20963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_20937])).
% 11.49/4.47  tff(c_20964, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(splitRight, [status(thm)], [c_18922])).
% 11.49/4.47  tff(c_177, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.49/4.47  tff(c_1768, plain, (![A_152, B_153]: (k4_xboole_0(A_152, B_153)=A_152 | ~r1_tarski(A_152, k4_xboole_0(A_152, B_153)))), inference(resolution, [status(thm)], [c_18, c_177])).
% 11.49/4.47  tff(c_1822, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=A_14 | ~r1_tarski(A_14, k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1768])).
% 11.49/4.47  tff(c_4108, plain, (![A_257, B_258]: (k3_xboole_0(A_257, B_258)=A_257 | ~r1_tarski(A_257, k3_xboole_0(A_257, B_258)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1822])).
% 11.49/4.47  tff(c_4130, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=B_2 | ~r1_tarski(B_2, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4108])).
% 11.49/4.47  tff(c_21034, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), '#skF_3')=k4_xboole_0('#skF_3', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20964, c_4130])).
% 11.49/4.47  tff(c_21153, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20964, c_2, c_21034])).
% 11.49/4.47  tff(c_21155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3499, c_21153])).
% 11.49/4.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/4.47  
% 11.49/4.47  Inference rules
% 11.49/4.47  ----------------------
% 11.49/4.47  #Ref     : 0
% 11.49/4.47  #Sup     : 5547
% 11.49/4.47  #Fact    : 0
% 11.49/4.47  #Define  : 0
% 11.49/4.47  #Split   : 10
% 11.49/4.47  #Chain   : 0
% 11.49/4.47  #Close   : 0
% 11.49/4.47  
% 11.49/4.47  Ordering : KBO
% 11.49/4.47  
% 11.49/4.47  Simplification rules
% 11.49/4.47  ----------------------
% 11.49/4.47  #Subsume      : 1277
% 11.49/4.47  #Demod        : 3120
% 11.49/4.47  #Tautology    : 2544
% 11.49/4.47  #SimpNegUnit  : 65
% 11.49/4.47  #BackRed      : 21
% 11.49/4.47  
% 11.49/4.47  #Partial instantiations: 0
% 11.49/4.47  #Strategies tried      : 1
% 11.49/4.47  
% 11.49/4.47  Timing (in seconds)
% 11.49/4.47  ----------------------
% 11.49/4.47  Preprocessing        : 0.30
% 11.49/4.47  Parsing              : 0.16
% 11.49/4.47  CNF conversion       : 0.02
% 11.49/4.47  Main loop            : 3.33
% 11.49/4.47  Inferencing          : 0.69
% 11.49/4.47  Reduction            : 1.55
% 11.49/4.47  Demodulation         : 1.26
% 11.49/4.47  BG Simplification    : 0.07
% 11.49/4.47  Subsumption          : 0.85
% 11.49/4.47  Abstraction          : 0.09
% 11.49/4.47  MUC search           : 0.00
% 11.49/4.47  Cooper               : 0.00
% 11.49/4.47  Total                : 3.66
% 11.49/4.47  Index Insertion      : 0.00
% 11.49/4.47  Index Deletion       : 0.00
% 11.49/4.47  Index Matching       : 0.00
% 11.49/4.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
