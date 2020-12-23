%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:00 EST 2020

% Result     : Theorem 9.55s
% Output     : CNFRefutation 9.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 293 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :   18
%              Number of atoms          :  146 ( 675 expanded)
%              Number of equality atoms :   74 ( 327 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_58,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | ~ r1_tarski(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    ! [A_43] : r2_hidden(A_43,k1_tarski(A_43)) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_120,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [C_28] :
      ( C_28 = '#skF_5'
      | ~ r2_hidden(C_28,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_125,plain,(
    ! [B_55] :
      ( '#skF_1'('#skF_4',B_55) = '#skF_5'
      | r1_tarski('#skF_4',B_55) ) ),
    inference(resolution,[status(thm)],[c_120,c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [C_64,B_65,A_66] :
      ( r2_hidden(C_64,B_65)
      | ~ r2_hidden(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_193,plain,(
    ! [A_1,B_2,B_65] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_65)
      | ~ r1_tarski(A_1,B_65)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_40,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_325,plain,(
    ! [E_91,C_92,B_93,A_94] :
      ( E_91 = C_92
      | E_91 = B_93
      | E_91 = A_94
      | ~ r2_hidden(E_91,k1_enumset1(A_94,B_93,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_645,plain,(
    ! [E_131,B_132,A_133] :
      ( E_131 = B_132
      | E_131 = A_133
      | E_131 = A_133
      | ~ r2_hidden(E_131,k2_tarski(A_133,B_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_325])).

tff(c_769,plain,(
    ! [E_140,A_141] :
      ( E_140 = A_141
      | E_140 = A_141
      | E_140 = A_141
      | ~ r2_hidden(E_140,k1_tarski(A_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_645])).

tff(c_1025,plain,(
    ! [A_165,A_166,B_167] :
      ( A_165 = '#skF_1'(A_166,B_167)
      | ~ r1_tarski(A_166,k1_tarski(A_165))
      | r1_tarski(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_193,c_769])).

tff(c_1114,plain,(
    ! [A_172,B_173] :
      ( A_172 = '#skF_1'('#skF_4',B_173)
      | r1_tarski('#skF_4',B_173)
      | '#skF_1'('#skF_4',k1_tarski(A_172)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_125,c_1025])).

tff(c_259,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),B_79) = k1_tarski(A_78)
      | r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_272,plain,(
    ! [B_79,A_78] :
      ( k1_xboole_0 = B_79
      | ~ r1_tarski(B_79,k1_tarski(A_78))
      | r2_hidden(A_78,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_14])).

tff(c_1992,plain,(
    ! [A_78,A_172] :
      ( k1_xboole_0 = '#skF_4'
      | r2_hidden(A_78,'#skF_4')
      | A_172 = '#skF_1'('#skF_4',k1_tarski(A_78))
      | '#skF_1'('#skF_4',k1_tarski(A_172)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1114,c_272])).

tff(c_2185,plain,(
    ! [A_78,A_172] :
      ( r2_hidden(A_78,'#skF_4')
      | A_172 = '#skF_1'('#skF_4',k1_tarski(A_78))
      | '#skF_1'('#skF_4',k1_tarski(A_172)) = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1992])).

tff(c_4320,plain,(
    ! [A_5708] :
      ( r2_hidden(A_5708,'#skF_4')
      | '#skF_1'('#skF_4',k1_tarski(A_5708)) = A_5708
      | A_5708 != '#skF_5' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2185])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4354,plain,(
    ! [A_5708] :
      ( ~ r2_hidden(A_5708,k1_tarski(A_5708))
      | r1_tarski('#skF_4',k1_tarski(A_5708))
      | r2_hidden(A_5708,'#skF_4')
      | A_5708 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4320,c_4])).

tff(c_4498,plain,(
    ! [A_5775] :
      ( r1_tarski('#skF_4',k1_tarski(A_5775))
      | r2_hidden(A_5775,'#skF_4')
      | A_5775 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4354])).

tff(c_4520,plain,(
    ! [A_5775] :
      ( k1_xboole_0 = '#skF_4'
      | r2_hidden(A_5775,'#skF_4')
      | A_5775 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_4498,c_272])).

tff(c_4544,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4520])).

tff(c_48,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_151,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_241,plain,(
    ! [B_77] :
      ( B_77 = '#skF_4'
      | ~ r1_tarski(B_77,'#skF_4')
      | '#skF_1'('#skF_4',B_77) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_125,c_151])).

tff(c_256,plain,(
    ! [A_23] :
      ( k1_tarski(A_23) = '#skF_4'
      | '#skF_1'('#skF_4',k1_tarski(A_23)) = '#skF_5'
      | ~ r2_hidden(A_23,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_241])).

tff(c_127,plain,(
    ! [B_56] :
      ( '#skF_1'('#skF_4',B_56) = '#skF_5'
      | r1_tarski('#skF_4',B_56) ) ),
    inference(resolution,[status(thm)],[c_120,c_54])).

tff(c_131,plain,(
    ! [B_9] :
      ( k1_xboole_0 = '#skF_4'
      | '#skF_1'('#skF_4',k4_xboole_0(B_9,'#skF_4')) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_127,c_14])).

tff(c_134,plain,(
    ! [B_9] : '#skF_1'('#skF_4',k4_xboole_0(B_9,'#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_131])).

tff(c_135,plain,(
    ! [B_57] : '#skF_1'('#skF_4',k4_xboole_0(B_57,'#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_131])).

tff(c_140,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_5','#skF_4')
      | r1_tarski('#skF_4',k4_xboole_0(B_57,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_6])).

tff(c_145,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_192,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_5',B_65)
      | ~ r1_tarski('#skF_4',B_65) ) ),
    inference(resolution,[status(thm)],[c_145,c_175])).

tff(c_722,plain,(
    ! [B_136,A_137] :
      ( B_136 = '#skF_5'
      | A_137 = '#skF_5'
      | ~ r1_tarski('#skF_4',k2_tarski(A_137,B_136)) ) ),
    inference(resolution,[status(thm)],[c_192,c_645])).

tff(c_728,plain,(
    ! [A_17] :
      ( A_17 = '#skF_5'
      | A_17 = '#skF_5'
      | ~ r1_tarski('#skF_4',k1_tarski(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_722])).

tff(c_13462,plain,(
    ! [A_22684,A_22685] :
      ( A_22684 = '#skF_5'
      | A_22685 = '#skF_1'('#skF_4',k1_tarski(A_22684))
      | '#skF_1'('#skF_4',k1_tarski(A_22685)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1114,c_728])).

tff(c_15021,plain,(
    ! [A_22684,B_9] :
      ( '#skF_1'('#skF_4',k1_tarski(A_22684)) = '#skF_5'
      | A_22684 = '#skF_5'
      | '#skF_1'('#skF_4',k1_tarski('#skF_1'('#skF_4',k4_xboole_0(B_9,'#skF_4')))) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13462,c_134])).

tff(c_15705,plain,(
    ! [A_22684] :
      ( '#skF_1'('#skF_4',k1_tarski(A_22684)) = '#skF_5'
      | A_22684 = '#skF_5'
      | '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_15021])).

tff(c_16829,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_15705])).

tff(c_16881,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16829,c_4])).

tff(c_17039,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_16881])).

tff(c_159,plain,(
    ! [A_23,B_24] :
      ( k1_tarski(A_23) = B_24
      | ~ r1_tarski(B_24,k1_tarski(A_23))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_17087,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_17039,c_159])).

tff(c_17121,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_17087])).

tff(c_17123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_17121])).

tff(c_17125,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15705])).

tff(c_17180,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_17125])).

tff(c_17198,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_17180])).

tff(c_17200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_17198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.55/3.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.55/3.48  
% 9.55/3.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.55/3.48  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 9.55/3.48  
% 9.55/3.48  %Foreground sorts:
% 9.55/3.48  
% 9.55/3.48  
% 9.55/3.48  %Background operators:
% 9.55/3.48  
% 9.55/3.48  
% 9.55/3.48  %Foreground operators:
% 9.55/3.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.55/3.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.55/3.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.55/3.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.55/3.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.55/3.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.55/3.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.55/3.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.55/3.48  tff('#skF_5', type, '#skF_5': $i).
% 9.55/3.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.55/3.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.55/3.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.55/3.48  tff('#skF_4', type, '#skF_4': $i).
% 9.55/3.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.55/3.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.55/3.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.55/3.48  
% 9.80/3.50  tff(f_87, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 9.80/3.50  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.80/3.50  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.80/3.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.80/3.50  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.80/3.50  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.80/3.50  tff(f_57, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.80/3.50  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 9.80/3.50  tff(f_42, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 9.80/3.50  tff(c_58, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.80/3.50  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.80/3.50  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.80/3.50  tff(c_75, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | ~r1_tarski(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.80/3.50  tff(c_80, plain, (![A_43]: (r2_hidden(A_43, k1_tarski(A_43)))), inference(resolution, [status(thm)], [c_12, c_75])).
% 9.80/3.50  tff(c_120, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.80/3.50  tff(c_54, plain, (![C_28]: (C_28='#skF_5' | ~r2_hidden(C_28, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.80/3.50  tff(c_125, plain, (![B_55]: ('#skF_1'('#skF_4', B_55)='#skF_5' | r1_tarski('#skF_4', B_55))), inference(resolution, [status(thm)], [c_120, c_54])).
% 9.80/3.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.80/3.50  tff(c_175, plain, (![C_64, B_65, A_66]: (r2_hidden(C_64, B_65) | ~r2_hidden(C_64, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.80/3.50  tff(c_193, plain, (![A_1, B_2, B_65]: (r2_hidden('#skF_1'(A_1, B_2), B_65) | ~r1_tarski(A_1, B_65) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_175])).
% 9.80/3.50  tff(c_40, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.80/3.50  tff(c_42, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.80/3.50  tff(c_325, plain, (![E_91, C_92, B_93, A_94]: (E_91=C_92 | E_91=B_93 | E_91=A_94 | ~r2_hidden(E_91, k1_enumset1(A_94, B_93, C_92)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.80/3.50  tff(c_645, plain, (![E_131, B_132, A_133]: (E_131=B_132 | E_131=A_133 | E_131=A_133 | ~r2_hidden(E_131, k2_tarski(A_133, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_325])).
% 9.80/3.50  tff(c_769, plain, (![E_140, A_141]: (E_140=A_141 | E_140=A_141 | E_140=A_141 | ~r2_hidden(E_140, k1_tarski(A_141)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_645])).
% 9.80/3.50  tff(c_1025, plain, (![A_165, A_166, B_167]: (A_165='#skF_1'(A_166, B_167) | ~r1_tarski(A_166, k1_tarski(A_165)) | r1_tarski(A_166, B_167))), inference(resolution, [status(thm)], [c_193, c_769])).
% 9.80/3.50  tff(c_1114, plain, (![A_172, B_173]: (A_172='#skF_1'('#skF_4', B_173) | r1_tarski('#skF_4', B_173) | '#skF_1'('#skF_4', k1_tarski(A_172))='#skF_5')), inference(resolution, [status(thm)], [c_125, c_1025])).
% 9.80/3.50  tff(c_259, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), B_79)=k1_tarski(A_78) | r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.80/3.50  tff(c_14, plain, (![A_8, B_9]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k4_xboole_0(B_9, A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.80/3.50  tff(c_272, plain, (![B_79, A_78]: (k1_xboole_0=B_79 | ~r1_tarski(B_79, k1_tarski(A_78)) | r2_hidden(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_259, c_14])).
% 9.80/3.50  tff(c_1992, plain, (![A_78, A_172]: (k1_xboole_0='#skF_4' | r2_hidden(A_78, '#skF_4') | A_172='#skF_1'('#skF_4', k1_tarski(A_78)) | '#skF_1'('#skF_4', k1_tarski(A_172))='#skF_5')), inference(resolution, [status(thm)], [c_1114, c_272])).
% 9.80/3.50  tff(c_2185, plain, (![A_78, A_172]: (r2_hidden(A_78, '#skF_4') | A_172='#skF_1'('#skF_4', k1_tarski(A_78)) | '#skF_1'('#skF_4', k1_tarski(A_172))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_1992])).
% 9.80/3.50  tff(c_4320, plain, (![A_5708]: (r2_hidden(A_5708, '#skF_4') | '#skF_1'('#skF_4', k1_tarski(A_5708))=A_5708 | A_5708!='#skF_5')), inference(factorization, [status(thm), theory('equality')], [c_2185])).
% 9.80/3.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.80/3.50  tff(c_4354, plain, (![A_5708]: (~r2_hidden(A_5708, k1_tarski(A_5708)) | r1_tarski('#skF_4', k1_tarski(A_5708)) | r2_hidden(A_5708, '#skF_4') | A_5708!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4320, c_4])).
% 9.80/3.50  tff(c_4498, plain, (![A_5775]: (r1_tarski('#skF_4', k1_tarski(A_5775)) | r2_hidden(A_5775, '#skF_4') | A_5775!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4354])).
% 9.80/3.50  tff(c_4520, plain, (![A_5775]: (k1_xboole_0='#skF_4' | r2_hidden(A_5775, '#skF_4') | A_5775!='#skF_5')), inference(resolution, [status(thm)], [c_4498, c_272])).
% 9.80/3.50  tff(c_4544, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_4520])).
% 9.80/3.50  tff(c_48, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.80/3.50  tff(c_151, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.80/3.50  tff(c_241, plain, (![B_77]: (B_77='#skF_4' | ~r1_tarski(B_77, '#skF_4') | '#skF_1'('#skF_4', B_77)='#skF_5')), inference(resolution, [status(thm)], [c_125, c_151])).
% 9.80/3.50  tff(c_256, plain, (![A_23]: (k1_tarski(A_23)='#skF_4' | '#skF_1'('#skF_4', k1_tarski(A_23))='#skF_5' | ~r2_hidden(A_23, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_241])).
% 9.80/3.50  tff(c_127, plain, (![B_56]: ('#skF_1'('#skF_4', B_56)='#skF_5' | r1_tarski('#skF_4', B_56))), inference(resolution, [status(thm)], [c_120, c_54])).
% 9.80/3.50  tff(c_131, plain, (![B_9]: (k1_xboole_0='#skF_4' | '#skF_1'('#skF_4', k4_xboole_0(B_9, '#skF_4'))='#skF_5')), inference(resolution, [status(thm)], [c_127, c_14])).
% 9.80/3.50  tff(c_134, plain, (![B_9]: ('#skF_1'('#skF_4', k4_xboole_0(B_9, '#skF_4'))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_131])).
% 9.80/3.50  tff(c_135, plain, (![B_57]: ('#skF_1'('#skF_4', k4_xboole_0(B_57, '#skF_4'))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_131])).
% 9.80/3.50  tff(c_140, plain, (![B_57]: (r2_hidden('#skF_5', '#skF_4') | r1_tarski('#skF_4', k4_xboole_0(B_57, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_135, c_6])).
% 9.80/3.50  tff(c_145, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_140])).
% 9.80/3.50  tff(c_192, plain, (![B_65]: (r2_hidden('#skF_5', B_65) | ~r1_tarski('#skF_4', B_65))), inference(resolution, [status(thm)], [c_145, c_175])).
% 9.80/3.50  tff(c_722, plain, (![B_136, A_137]: (B_136='#skF_5' | A_137='#skF_5' | ~r1_tarski('#skF_4', k2_tarski(A_137, B_136)))), inference(resolution, [status(thm)], [c_192, c_645])).
% 9.80/3.50  tff(c_728, plain, (![A_17]: (A_17='#skF_5' | A_17='#skF_5' | ~r1_tarski('#skF_4', k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_722])).
% 9.80/3.50  tff(c_13462, plain, (![A_22684, A_22685]: (A_22684='#skF_5' | A_22685='#skF_1'('#skF_4', k1_tarski(A_22684)) | '#skF_1'('#skF_4', k1_tarski(A_22685))='#skF_5')), inference(resolution, [status(thm)], [c_1114, c_728])).
% 9.80/3.50  tff(c_15021, plain, (![A_22684, B_9]: ('#skF_1'('#skF_4', k1_tarski(A_22684))='#skF_5' | A_22684='#skF_5' | '#skF_1'('#skF_4', k1_tarski('#skF_1'('#skF_4', k4_xboole_0(B_9, '#skF_4'))))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13462, c_134])).
% 9.80/3.50  tff(c_15705, plain, (![A_22684]: ('#skF_1'('#skF_4', k1_tarski(A_22684))='#skF_5' | A_22684='#skF_5' | '#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_15021])).
% 9.80/3.50  tff(c_16829, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(splitLeft, [status(thm)], [c_15705])).
% 9.80/3.50  tff(c_16881, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16829, c_4])).
% 9.80/3.50  tff(c_17039, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_16881])).
% 9.80/3.50  tff(c_159, plain, (![A_23, B_24]: (k1_tarski(A_23)=B_24 | ~r1_tarski(B_24, k1_tarski(A_23)) | ~r2_hidden(A_23, B_24))), inference(resolution, [status(thm)], [c_48, c_151])).
% 9.80/3.50  tff(c_17087, plain, (k1_tarski('#skF_5')='#skF_4' | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_17039, c_159])).
% 9.80/3.50  tff(c_17121, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_17087])).
% 9.80/3.50  tff(c_17123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_17121])).
% 9.80/3.50  tff(c_17125, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))!='#skF_5'), inference(splitRight, [status(thm)], [c_15705])).
% 9.80/3.50  tff(c_17180, plain, (k1_tarski('#skF_5')='#skF_4' | ~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_256, c_17125])).
% 9.80/3.50  tff(c_17198, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_17180])).
% 9.80/3.50  tff(c_17200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_17198])).
% 9.80/3.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.80/3.50  
% 9.80/3.50  Inference rules
% 9.80/3.50  ----------------------
% 9.80/3.50  #Ref     : 1
% 9.80/3.50  #Sup     : 2958
% 9.80/3.50  #Fact    : 44
% 9.80/3.50  #Define  : 0
% 9.80/3.50  #Split   : 3
% 9.80/3.50  #Chain   : 0
% 9.80/3.50  #Close   : 0
% 9.80/3.50  
% 9.80/3.50  Ordering : KBO
% 9.80/3.50  
% 9.80/3.50  Simplification rules
% 9.80/3.50  ----------------------
% 9.80/3.50  #Subsume      : 1124
% 9.80/3.50  #Demod        : 215
% 9.80/3.50  #Tautology    : 402
% 9.80/3.50  #SimpNegUnit  : 37
% 9.80/3.50  #BackRed      : 0
% 9.80/3.50  
% 9.80/3.50  #Partial instantiations: 13244
% 9.80/3.50  #Strategies tried      : 1
% 9.80/3.50  
% 9.80/3.50  Timing (in seconds)
% 9.80/3.50  ----------------------
% 9.80/3.50  Preprocessing        : 0.31
% 9.80/3.50  Parsing              : 0.16
% 9.80/3.50  CNF conversion       : 0.02
% 9.80/3.50  Main loop            : 2.41
% 9.80/3.50  Inferencing          : 0.89
% 9.80/3.50  Reduction            : 0.49
% 9.80/3.50  Demodulation         : 0.32
% 9.80/3.51  BG Simplification    : 0.09
% 9.80/3.51  Subsumption          : 0.83
% 9.80/3.51  Abstraction          : 0.10
% 9.80/3.51  MUC search           : 0.00
% 9.80/3.51  Cooper               : 0.00
% 9.80/3.51  Total                : 2.75
% 9.80/3.51  Index Insertion      : 0.00
% 9.80/3.51  Index Deletion       : 0.00
% 9.80/3.51  Index Matching       : 0.00
% 9.80/3.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
