%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:06 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 118 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :   90 ( 151 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_28,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_62,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_204,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = A_60
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_231,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62,c_204])).

tff(c_344,plain,(
    ! [D_67,B_68,A_69] :
      ( ~ r2_hidden(D_67,B_68)
      | ~ r2_hidden(D_67,k4_xboole_0(A_69,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_361,plain,(
    ! [D_72] :
      ( ~ r2_hidden(D_72,'#skF_4')
      | ~ r2_hidden(D_72,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_344])).

tff(c_365,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_361])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_730,plain,(
    ! [A_105,B_106] : k4_xboole_0(A_105,k4_xboole_0(A_105,B_106)) = k3_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [A_21] : r1_xboole_0(k1_xboole_0,A_21) ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_228,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_204])).

tff(c_840,plain,(
    ! [B_108] : k3_xboole_0(k1_xboole_0,B_108) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_228])).

tff(c_880,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_840])).

tff(c_797,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_730])).

tff(c_1059,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_797])).

tff(c_58,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,k1_tarski(B_38)) = A_37
      | r2_hidden(B_38,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_774,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,A_37) = k3_xboole_0(A_37,k1_tarski(B_38))
      | r2_hidden(B_38,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_730])).

tff(c_10286,plain,(
    ! [A_295,B_296] :
      ( k3_xboole_0(A_295,k1_tarski(B_296)) = k1_xboole_0
      | r2_hidden(B_296,A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_774])).

tff(c_1191,plain,(
    ! [A_117,B_118,C_119] : k3_xboole_0(k3_xboole_0(A_117,B_118),C_119) = k3_xboole_0(A_117,k3_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9065,plain,(
    ! [B_275,A_276,C_277] : k3_xboole_0(k3_xboole_0(B_275,A_276),C_277) = k3_xboole_0(A_276,k3_xboole_0(B_275,C_277)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1191])).

tff(c_66,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_67,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_162,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_166,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_162])).

tff(c_9272,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',k1_tarski('#skF_6'))) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9065,c_166])).

tff(c_10300,plain,
    ( k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10286,c_9272])).

tff(c_10492,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_10300])).

tff(c_10493,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_10492])).

tff(c_567,plain,(
    ! [A_98,B_99] : k4_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_605,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_567])).

tff(c_10577,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10493,c_605])).

tff(c_10622,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10577])).

tff(c_42,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_99,plain,(
    ! [B_26,A_25] : r1_xboole_0(B_26,k4_xboole_0(A_25,B_26)) ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_10685,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10622,c_99])).

tff(c_100,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_92])).

tff(c_1669,plain,(
    ! [A_131,C_132,B_133] :
      ( ~ r1_xboole_0(A_131,C_132)
      | ~ r1_xboole_0(A_131,B_133)
      | r1_xboole_0(A_131,k2_xboole_0(B_133,C_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13696,plain,(
    ! [B_325,C_326,A_327] :
      ( r1_xboole_0(k2_xboole_0(B_325,C_326),A_327)
      | ~ r1_xboole_0(A_327,C_326)
      | ~ r1_xboole_0(A_327,B_325) ) ),
    inference(resolution,[status(thm)],[c_1669,c_22])).

tff(c_60,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_13712,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_13696,c_60])).

tff(c_13723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10685,c_100,c_13712])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.87  
% 7.68/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 7.68/2.87  
% 7.68/2.87  %Foreground sorts:
% 7.68/2.87  
% 7.68/2.87  
% 7.68/2.87  %Background operators:
% 7.68/2.87  
% 7.68/2.87  
% 7.68/2.87  %Foreground operators:
% 7.68/2.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.68/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.68/2.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.68/2.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.68/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.68/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.68/2.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.68/2.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.68/2.87  tff('#skF_5', type, '#skF_5': $i).
% 7.68/2.87  tff('#skF_6', type, '#skF_6': $i).
% 7.68/2.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.68/2.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.68/2.87  tff('#skF_3', type, '#skF_3': $i).
% 7.68/2.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.68/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.68/2.87  tff('#skF_4', type, '#skF_4': $i).
% 7.68/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.68/2.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.68/2.87  
% 7.68/2.89  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.68/2.89  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.68/2.89  tff(f_77, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.68/2.89  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.68/2.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.68/2.89  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.68/2.89  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.68/2.89  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.68/2.89  tff(f_90, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.68/2.89  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.68/2.89  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.68/2.89  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.68/2.89  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.68/2.89  tff(f_71, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.68/2.89  tff(c_28, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.68/2.89  tff(c_64, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.68/2.89  tff(c_62, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.68/2.89  tff(c_204, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=A_60 | ~r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.68/2.89  tff(c_231, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_62, c_204])).
% 7.68/2.89  tff(c_344, plain, (![D_67, B_68, A_69]: (~r2_hidden(D_67, B_68) | ~r2_hidden(D_67, k4_xboole_0(A_69, B_68)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.89  tff(c_361, plain, (![D_72]: (~r2_hidden(D_72, '#skF_4') | ~r2_hidden(D_72, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_344])).
% 7.68/2.89  tff(c_365, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_361])).
% 7.68/2.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.68/2.89  tff(c_730, plain, (![A_105, B_106]: (k4_xboole_0(A_105, k4_xboole_0(A_105, B_106))=k3_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.68/2.89  tff(c_34, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.68/2.89  tff(c_92, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.68/2.89  tff(c_101, plain, (![A_21]: (r1_xboole_0(k1_xboole_0, A_21))), inference(resolution, [status(thm)], [c_34, c_92])).
% 7.68/2.89  tff(c_228, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_101, c_204])).
% 7.68/2.89  tff(c_840, plain, (![B_108]: (k3_xboole_0(k1_xboole_0, B_108)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_730, c_228])).
% 7.68/2.89  tff(c_880, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_840])).
% 7.68/2.89  tff(c_797, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_730])).
% 7.68/2.89  tff(c_1059, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_880, c_797])).
% 7.68/2.89  tff(c_58, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k1_tarski(B_38))=A_37 | r2_hidden(B_38, A_37))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.68/2.89  tff(c_774, plain, (![A_37, B_38]: (k4_xboole_0(A_37, A_37)=k3_xboole_0(A_37, k1_tarski(B_38)) | r2_hidden(B_38, A_37))), inference(superposition, [status(thm), theory('equality')], [c_58, c_730])).
% 7.68/2.89  tff(c_10286, plain, (![A_295, B_296]: (k3_xboole_0(A_295, k1_tarski(B_296))=k1_xboole_0 | r2_hidden(B_296, A_295))), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_774])).
% 7.68/2.89  tff(c_1191, plain, (![A_117, B_118, C_119]: (k3_xboole_0(k3_xboole_0(A_117, B_118), C_119)=k3_xboole_0(A_117, k3_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.68/2.89  tff(c_9065, plain, (![B_275, A_276, C_277]: (k3_xboole_0(k3_xboole_0(B_275, A_276), C_277)=k3_xboole_0(A_276, k3_xboole_0(B_275, C_277)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1191])).
% 7.68/2.89  tff(c_66, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.68/2.89  tff(c_67, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 7.68/2.89  tff(c_162, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.68/2.89  tff(c_166, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_67, c_162])).
% 7.68/2.89  tff(c_9272, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', k1_tarski('#skF_6')))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9065, c_166])).
% 7.68/2.89  tff(c_10300, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10286, c_9272])).
% 7.68/2.89  tff(c_10492, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_880, c_10300])).
% 7.68/2.89  tff(c_10493, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_365, c_10492])).
% 7.68/2.89  tff(c_567, plain, (![A_98, B_99]: (k4_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.68/2.89  tff(c_605, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_567])).
% 7.68/2.89  tff(c_10577, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10493, c_605])).
% 7.68/2.89  tff(c_10622, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10577])).
% 7.68/2.89  tff(c_42, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.68/2.89  tff(c_99, plain, (![B_26, A_25]: (r1_xboole_0(B_26, k4_xboole_0(A_25, B_26)))), inference(resolution, [status(thm)], [c_42, c_92])).
% 7.68/2.89  tff(c_10685, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10622, c_99])).
% 7.68/2.89  tff(c_100, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_92])).
% 7.68/2.89  tff(c_1669, plain, (![A_131, C_132, B_133]: (~r1_xboole_0(A_131, C_132) | ~r1_xboole_0(A_131, B_133) | r1_xboole_0(A_131, k2_xboole_0(B_133, C_132)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.68/2.89  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.68/2.89  tff(c_13696, plain, (![B_325, C_326, A_327]: (r1_xboole_0(k2_xboole_0(B_325, C_326), A_327) | ~r1_xboole_0(A_327, C_326) | ~r1_xboole_0(A_327, B_325))), inference(resolution, [status(thm)], [c_1669, c_22])).
% 7.68/2.89  tff(c_60, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.68/2.89  tff(c_13712, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_13696, c_60])).
% 7.68/2.89  tff(c_13723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10685, c_100, c_13712])).
% 7.68/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.89  
% 7.68/2.89  Inference rules
% 7.68/2.89  ----------------------
% 7.68/2.89  #Ref     : 0
% 7.68/2.89  #Sup     : 3394
% 7.68/2.89  #Fact    : 0
% 7.68/2.89  #Define  : 0
% 7.68/2.89  #Split   : 0
% 7.68/2.89  #Chain   : 0
% 7.68/2.89  #Close   : 0
% 7.68/2.89  
% 7.68/2.89  Ordering : KBO
% 7.68/2.89  
% 7.68/2.89  Simplification rules
% 7.68/2.89  ----------------------
% 7.68/2.89  #Subsume      : 116
% 7.68/2.89  #Demod        : 3110
% 7.68/2.89  #Tautology    : 2477
% 7.68/2.89  #SimpNegUnit  : 18
% 7.68/2.89  #BackRed      : 21
% 7.68/2.89  
% 7.68/2.89  #Partial instantiations: 0
% 7.68/2.89  #Strategies tried      : 1
% 7.68/2.89  
% 7.68/2.89  Timing (in seconds)
% 7.68/2.89  ----------------------
% 7.83/2.89  Preprocessing        : 0.36
% 7.83/2.89  Parsing              : 0.19
% 7.83/2.89  CNF conversion       : 0.02
% 7.83/2.89  Main loop            : 1.76
% 7.83/2.89  Inferencing          : 0.43
% 7.83/2.89  Reduction            : 0.88
% 7.83/2.89  Demodulation         : 0.73
% 7.83/2.89  BG Simplification    : 0.05
% 7.83/2.89  Subsumption          : 0.30
% 7.83/2.89  Abstraction          : 0.06
% 7.83/2.89  MUC search           : 0.00
% 7.83/2.89  Cooper               : 0.00
% 7.83/2.89  Total                : 2.15
% 7.83/2.89  Index Insertion      : 0.00
% 7.83/2.89  Index Deletion       : 0.00
% 7.83/2.89  Index Matching       : 0.00
% 7.83/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
