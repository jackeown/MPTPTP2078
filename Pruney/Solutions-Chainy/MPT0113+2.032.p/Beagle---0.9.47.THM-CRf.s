%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :   64 (  89 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 119 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_55,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_311,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | k4_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_323,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_56])).

tff(c_34,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_168,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_868,plain,(
    ! [A_79,B_80] : k3_xboole_0(k3_xboole_0(A_79,B_80),A_79) = k3_xboole_0(A_79,B_80) ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1380,plain,(
    ! [A_94,B_95] : k3_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_2])).

tff(c_106,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_123,plain,(
    ! [A_39,B_40] : k4_xboole_0(k3_xboole_0(A_39,B_40),A_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_106])).

tff(c_38,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_128,plain,(
    ! [A_39,B_40] : r1_tarski(k1_xboole_0,k3_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_38])).

tff(c_188,plain,(
    ! [A_39,B_40] : k3_xboole_0(k1_xboole_0,k3_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128,c_168])).

tff(c_1503,plain,(
    ! [B_96] : k3_xboole_0(k1_xboole_0,B_96) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1380,c_188])).

tff(c_1552,plain,(
    ! [B_96] : k3_xboole_0(B_96,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_2])).

tff(c_122,plain,(
    ! [A_22,B_23] : k4_xboole_0(k4_xboole_0(A_22,B_23),A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_191,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_168])).

tff(c_1585,plain,(
    ! [A_97,B_98,C_99] : k4_xboole_0(k3_xboole_0(A_97,B_98),C_99) = k3_xboole_0(A_97,k4_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1790,plain,(
    ! [C_102] : k3_xboole_0('#skF_4',k4_xboole_0(k4_xboole_0('#skF_5','#skF_6'),C_102)) = k4_xboole_0('#skF_4',C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_1585])).

tff(c_1841,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_1790])).

tff(c_1853,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1841])).

tff(c_1855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_1853])).

tff(c_1856,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1857,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2134,plain,(
    ! [A_123,B_124] :
      ( k3_xboole_0(A_123,B_124) = A_123
      | ~ r1_tarski(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2171,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1857,c_2134])).

tff(c_3497,plain,(
    ! [A_167,B_168,C_169] : k4_xboole_0(k3_xboole_0(A_167,B_168),C_169) = k3_xboole_0(A_167,k4_xboole_0(B_168,C_169)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4186,plain,(
    ! [C_187] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_187)) = k4_xboole_0('#skF_4',C_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_3497])).

tff(c_2173,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_2134])).

tff(c_4227,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4186,c_2173])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2506,plain,(
    ! [D_135,B_136,A_137] :
      ( ~ r2_hidden(D_135,B_136)
      | ~ r2_hidden(D_135,k4_xboole_0(A_137,B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13484,plain,(
    ! [A_307,B_308,B_309] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_307,B_308),B_309),B_308)
      | r1_xboole_0(k4_xboole_0(A_307,B_308),B_309) ) ),
    inference(resolution,[status(thm)],[c_26,c_2506])).

tff(c_13623,plain,(
    ! [A_311,B_312] : r1_xboole_0(k4_xboole_0(A_311,B_312),B_312) ),
    inference(resolution,[status(thm)],[c_24,c_13484])).

tff(c_13679,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4227,c_13623])).

tff(c_13713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1856,c_13679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.67  
% 7.38/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.38/2.67  
% 7.38/2.67  %Foreground sorts:
% 7.38/2.67  
% 7.38/2.67  
% 7.38/2.67  %Background operators:
% 7.38/2.67  
% 7.38/2.67  
% 7.38/2.67  %Foreground operators:
% 7.38/2.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.38/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.38/2.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.38/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.38/2.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.38/2.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.38/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.38/2.67  tff('#skF_5', type, '#skF_5': $i).
% 7.38/2.67  tff('#skF_6', type, '#skF_6': $i).
% 7.38/2.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.38/2.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.38/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.38/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.38/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.38/2.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.38/2.67  
% 7.60/2.69  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.60/2.69  tff(f_80, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.60/2.69  tff(f_63, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.60/2.69  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.60/2.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.60/2.69  tff(f_69, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.60/2.69  tff(f_71, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.60/2.69  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.60/2.69  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.60/2.69  tff(c_311, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | k4_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.60/2.69  tff(c_44, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.60/2.69  tff(c_56, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 7.60/2.69  tff(c_323, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_311, c_56])).
% 7.60/2.69  tff(c_34, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.60/2.69  tff(c_168, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.60/2.69  tff(c_868, plain, (![A_79, B_80]: (k3_xboole_0(k3_xboole_0(A_79, B_80), A_79)=k3_xboole_0(A_79, B_80))), inference(resolution, [status(thm)], [c_34, c_168])).
% 7.60/2.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.60/2.69  tff(c_1380, plain, (![A_94, B_95]: (k3_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_868, c_2])).
% 7.60/2.69  tff(c_106, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.60/2.69  tff(c_123, plain, (![A_39, B_40]: (k4_xboole_0(k3_xboole_0(A_39, B_40), A_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_106])).
% 7.60/2.69  tff(c_38, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.60/2.69  tff(c_128, plain, (![A_39, B_40]: (r1_tarski(k1_xboole_0, k3_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_38])).
% 7.60/2.69  tff(c_188, plain, (![A_39, B_40]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(A_39, B_40))=k1_xboole_0)), inference(resolution, [status(thm)], [c_128, c_168])).
% 7.60/2.69  tff(c_1503, plain, (![B_96]: (k3_xboole_0(k1_xboole_0, B_96)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1380, c_188])).
% 7.60/2.69  tff(c_1552, plain, (![B_96]: (k3_xboole_0(B_96, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1503, c_2])).
% 7.60/2.69  tff(c_122, plain, (![A_22, B_23]: (k4_xboole_0(k4_xboole_0(A_22, B_23), A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_106])).
% 7.60/2.69  tff(c_46, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.60/2.69  tff(c_191, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_168])).
% 7.60/2.69  tff(c_1585, plain, (![A_97, B_98, C_99]: (k4_xboole_0(k3_xboole_0(A_97, B_98), C_99)=k3_xboole_0(A_97, k4_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.60/2.69  tff(c_1790, plain, (![C_102]: (k3_xboole_0('#skF_4', k4_xboole_0(k4_xboole_0('#skF_5', '#skF_6'), C_102))=k4_xboole_0('#skF_4', C_102))), inference(superposition, [status(thm), theory('equality')], [c_191, c_1585])).
% 7.60/2.69  tff(c_1841, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_122, c_1790])).
% 7.60/2.69  tff(c_1853, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_1841])).
% 7.60/2.69  tff(c_1855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_1853])).
% 7.60/2.69  tff(c_1856, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 7.60/2.69  tff(c_1857, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 7.60/2.69  tff(c_2134, plain, (![A_123, B_124]: (k3_xboole_0(A_123, B_124)=A_123 | ~r1_tarski(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.60/2.69  tff(c_2171, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_1857, c_2134])).
% 7.60/2.69  tff(c_3497, plain, (![A_167, B_168, C_169]: (k4_xboole_0(k3_xboole_0(A_167, B_168), C_169)=k3_xboole_0(A_167, k4_xboole_0(B_168, C_169)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.60/2.69  tff(c_4186, plain, (![C_187]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_187))=k4_xboole_0('#skF_4', C_187))), inference(superposition, [status(thm), theory('equality')], [c_2171, c_3497])).
% 7.60/2.69  tff(c_2173, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_2134])).
% 7.60/2.69  tff(c_4227, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4186, c_2173])).
% 7.60/2.69  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.60/2.69  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.60/2.69  tff(c_2506, plain, (![D_135, B_136, A_137]: (~r2_hidden(D_135, B_136) | ~r2_hidden(D_135, k4_xboole_0(A_137, B_136)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.60/2.69  tff(c_13484, plain, (![A_307, B_308, B_309]: (~r2_hidden('#skF_3'(k4_xboole_0(A_307, B_308), B_309), B_308) | r1_xboole_0(k4_xboole_0(A_307, B_308), B_309))), inference(resolution, [status(thm)], [c_26, c_2506])).
% 7.60/2.69  tff(c_13623, plain, (![A_311, B_312]: (r1_xboole_0(k4_xboole_0(A_311, B_312), B_312))), inference(resolution, [status(thm)], [c_24, c_13484])).
% 7.60/2.69  tff(c_13679, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4227, c_13623])).
% 7.60/2.69  tff(c_13713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1856, c_13679])).
% 7.60/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.69  
% 7.60/2.69  Inference rules
% 7.60/2.69  ----------------------
% 7.60/2.69  #Ref     : 0
% 7.60/2.69  #Sup     : 3496
% 7.60/2.69  #Fact    : 0
% 7.60/2.69  #Define  : 0
% 7.60/2.69  #Split   : 2
% 7.60/2.69  #Chain   : 0
% 7.60/2.69  #Close   : 0
% 7.60/2.69  
% 7.60/2.69  Ordering : KBO
% 7.60/2.69  
% 7.60/2.69  Simplification rules
% 7.60/2.69  ----------------------
% 7.60/2.69  #Subsume      : 171
% 7.60/2.69  #Demod        : 3610
% 7.60/2.69  #Tautology    : 2433
% 7.60/2.69  #SimpNegUnit  : 2
% 7.60/2.69  #BackRed      : 4
% 7.60/2.69  
% 7.60/2.69  #Partial instantiations: 0
% 7.60/2.69  #Strategies tried      : 1
% 7.60/2.69  
% 7.60/2.69  Timing (in seconds)
% 7.60/2.69  ----------------------
% 7.60/2.69  Preprocessing        : 0.32
% 7.60/2.69  Parsing              : 0.17
% 7.60/2.69  CNF conversion       : 0.02
% 7.60/2.69  Main loop            : 1.60
% 7.60/2.69  Inferencing          : 0.43
% 7.60/2.69  Reduction            : 0.76
% 7.60/2.69  Demodulation         : 0.64
% 7.60/2.69  BG Simplification    : 0.05
% 7.60/2.69  Subsumption          : 0.25
% 7.60/2.69  Abstraction          : 0.07
% 7.60/2.69  MUC search           : 0.00
% 7.60/2.69  Cooper               : 0.00
% 7.60/2.69  Total                : 1.95
% 7.60/2.69  Index Insertion      : 0.00
% 7.60/2.69  Index Deletion       : 0.00
% 7.60/2.69  Index Matching       : 0.00
% 7.60/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
