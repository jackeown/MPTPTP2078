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
% DateTime   : Thu Dec  3 10:08:44 EST 2020

% Result     : Theorem 11.09s
% Output     : CNFRefutation 11.09s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 104 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 173 expanded)
%              Number of equality atoms :   24 (  49 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [A_32] : k3_xboole_0(k1_xboole_0,A_32) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_36,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_149,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_161,plain,(
    ! [A_17,C_39] :
      ( ~ r1_xboole_0(A_17,k1_xboole_0)
      | ~ r2_hidden(C_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_149])).

tff(c_163,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_161])).

tff(c_227,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_5'(A_50,B_51),k3_xboole_0(A_50,B_51))
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_5'(k1_xboole_0,A_32),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_227])).

tff(c_256,plain,(
    ! [A_32] : r1_xboole_0(k1_xboole_0,A_32) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_242])).

tff(c_550,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_3'(A_86,B_87),B_87)
      | r2_hidden('#skF_4'(A_86,B_87),A_86)
      | B_87 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6094,plain,(
    ! [A_248,B_249,B_250] :
      ( ~ r1_xboole_0(A_248,B_249)
      | r2_hidden('#skF_3'(k3_xboole_0(A_248,B_249),B_250),B_250)
      | k3_xboole_0(A_248,B_249) = B_250 ) ),
    inference(resolution,[status(thm)],[c_550,c_32])).

tff(c_6184,plain,(
    ! [A_32,B_250] :
      ( ~ r1_xboole_0(k1_xboole_0,A_32)
      | r2_hidden('#skF_3'(k1_xboole_0,B_250),B_250)
      | k3_xboole_0(k1_xboole_0,A_32) = B_250 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6094])).

tff(c_6208,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_250),B_250)
      | k1_xboole_0 = B_250 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_256,c_6184])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1296,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_1'(A_113,B_114,C_115),B_114)
      | r2_hidden('#skF_2'(A_113,B_114,C_115),C_115)
      | k3_xboole_0(A_113,B_114) = C_115 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8075,plain,(
    ! [A_311,B_312,A_313,B_314] :
      ( ~ r1_xboole_0(A_311,B_312)
      | r2_hidden('#skF_1'(A_313,B_314,k3_xboole_0(A_311,B_312)),B_314)
      | k3_xboole_0(A_313,B_314) = k3_xboole_0(A_311,B_312) ) ),
    inference(resolution,[status(thm)],[c_1296,c_32])).

tff(c_8177,plain,(
    ! [A_17,A_313,B_314] :
      ( ~ r1_xboole_0(A_17,k1_xboole_0)
      | r2_hidden('#skF_1'(A_313,B_314,k1_xboole_0),B_314)
      | k3_xboole_0(A_313,B_314) = k3_xboole_0(A_17,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8075])).

tff(c_8196,plain,(
    ! [A_313,B_314] :
      ( r2_hidden('#skF_1'(A_313,B_314,k1_xboole_0),B_314)
      | k3_xboole_0(A_313,B_314) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_8177])).

tff(c_1613,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_hidden('#skF_1'(A_128,B_129,C_130),A_128)
      | r2_hidden('#skF_2'(A_128,B_129,C_130),C_130)
      | k3_xboole_0(A_128,B_129) = C_130 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [D_25,A_19,B_20] :
      ( ~ r2_hidden(D_25,'#skF_6'(A_19,B_20))
      | ~ r2_hidden(D_25,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20547,plain,(
    ! [A_493,B_494,B_495,C_496] :
      ( ~ r2_hidden('#skF_1'('#skF_6'(A_493,B_494),B_495,C_496),B_494)
      | ~ r2_hidden(A_493,B_494)
      | r2_hidden('#skF_2'('#skF_6'(A_493,B_494),B_495,C_496),C_496)
      | k3_xboole_0('#skF_6'(A_493,B_494),B_495) = C_496 ) ),
    inference(resolution,[status(thm)],[c_1613,c_38])).

tff(c_20562,plain,(
    ! [A_493,B_314] :
      ( ~ r2_hidden(A_493,B_314)
      | r2_hidden('#skF_2'('#skF_6'(A_493,B_314),B_314,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0('#skF_6'(A_493,B_314),B_314) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8196,c_20547])).

tff(c_20582,plain,(
    ! [A_493,B_314] :
      ( ~ r2_hidden(A_493,B_314)
      | r2_hidden('#skF_2'('#skF_6'(A_493,B_314),B_314,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(B_314,'#skF_6'(A_493,B_314)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20562])).

tff(c_20591,plain,(
    ! [A_497,B_498] :
      ( ~ r2_hidden(A_497,B_498)
      | k3_xboole_0(B_498,'#skF_6'(A_497,B_498)) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_20582])).

tff(c_248,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_5'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_20994,plain,(
    ! [A_497,B_498] :
      ( r2_hidden('#skF_5'('#skF_6'(A_497,B_498),B_498),k1_xboole_0)
      | r1_xboole_0('#skF_6'(A_497,B_498),B_498)
      | ~ r2_hidden(A_497,B_498) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20591,c_248])).

tff(c_21136,plain,(
    ! [A_499,B_500] :
      ( r1_xboole_0('#skF_6'(A_499,B_500),B_500)
      | ~ r2_hidden(A_499,B_500) ) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_20994])).

tff(c_166,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_6'(A_41,B_42),B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [B_27] :
      ( ~ r1_xboole_0(B_27,'#skF_7')
      | ~ r2_hidden(B_27,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_186,plain,(
    ! [A_41] :
      ( ~ r1_xboole_0('#skF_6'(A_41,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_41,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_166,c_42])).

tff(c_21161,plain,(
    ! [A_501] : ~ r2_hidden(A_501,'#skF_7') ),
    inference(resolution,[status(thm)],[c_21136,c_186])).

tff(c_21337,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6208,c_21161])).

tff(c_21476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_21337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.09/4.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.38  
% 11.09/4.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.39  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 11.09/4.39  
% 11.09/4.39  %Foreground sorts:
% 11.09/4.39  
% 11.09/4.39  
% 11.09/4.39  %Background operators:
% 11.09/4.39  
% 11.09/4.39  
% 11.09/4.39  %Foreground operators:
% 11.09/4.39  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.09/4.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.09/4.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.09/4.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.09/4.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.09/4.39  tff('#skF_7', type, '#skF_7': $i).
% 11.09/4.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.09/4.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.09/4.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.09/4.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.09/4.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.09/4.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.09/4.39  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.09/4.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.09/4.39  
% 11.09/4.40  tff(f_85, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 11.09/4.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.09/4.40  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.09/4.40  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.09/4.40  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.09/4.40  tff(f_43, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 11.09/4.40  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.09/4.40  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 11.09/4.40  tff(c_44, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.09/4.40  tff(c_54, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.09/4.40  tff(c_34, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.09/4.40  tff(c_70, plain, (![A_32]: (k3_xboole_0(k1_xboole_0, A_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_34])).
% 11.09/4.40  tff(c_36, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.09/4.40  tff(c_149, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.09/4.40  tff(c_161, plain, (![A_17, C_39]: (~r1_xboole_0(A_17, k1_xboole_0) | ~r2_hidden(C_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_149])).
% 11.09/4.40  tff(c_163, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_161])).
% 11.09/4.40  tff(c_227, plain, (![A_50, B_51]: (r2_hidden('#skF_5'(A_50, B_51), k3_xboole_0(A_50, B_51)) | r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.09/4.40  tff(c_242, plain, (![A_32]: (r2_hidden('#skF_5'(k1_xboole_0, A_32), k1_xboole_0) | r1_xboole_0(k1_xboole_0, A_32))), inference(superposition, [status(thm), theory('equality')], [c_70, c_227])).
% 11.09/4.40  tff(c_256, plain, (![A_32]: (r1_xboole_0(k1_xboole_0, A_32))), inference(negUnitSimplification, [status(thm)], [c_163, c_242])).
% 11.09/4.40  tff(c_550, plain, (![A_86, B_87]: (r2_hidden('#skF_3'(A_86, B_87), B_87) | r2_hidden('#skF_4'(A_86, B_87), A_86) | B_87=A_86)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.09/4.40  tff(c_32, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.09/4.40  tff(c_6094, plain, (![A_248, B_249, B_250]: (~r1_xboole_0(A_248, B_249) | r2_hidden('#skF_3'(k3_xboole_0(A_248, B_249), B_250), B_250) | k3_xboole_0(A_248, B_249)=B_250)), inference(resolution, [status(thm)], [c_550, c_32])).
% 11.09/4.40  tff(c_6184, plain, (![A_32, B_250]: (~r1_xboole_0(k1_xboole_0, A_32) | r2_hidden('#skF_3'(k1_xboole_0, B_250), B_250) | k3_xboole_0(k1_xboole_0, A_32)=B_250)), inference(superposition, [status(thm), theory('equality')], [c_70, c_6094])).
% 11.09/4.40  tff(c_6208, plain, (![B_250]: (r2_hidden('#skF_3'(k1_xboole_0, B_250), B_250) | k1_xboole_0=B_250)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_256, c_6184])).
% 11.09/4.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.09/4.40  tff(c_1296, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_1'(A_113, B_114, C_115), B_114) | r2_hidden('#skF_2'(A_113, B_114, C_115), C_115) | k3_xboole_0(A_113, B_114)=C_115)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.09/4.40  tff(c_8075, plain, (![A_311, B_312, A_313, B_314]: (~r1_xboole_0(A_311, B_312) | r2_hidden('#skF_1'(A_313, B_314, k3_xboole_0(A_311, B_312)), B_314) | k3_xboole_0(A_313, B_314)=k3_xboole_0(A_311, B_312))), inference(resolution, [status(thm)], [c_1296, c_32])).
% 11.09/4.40  tff(c_8177, plain, (![A_17, A_313, B_314]: (~r1_xboole_0(A_17, k1_xboole_0) | r2_hidden('#skF_1'(A_313, B_314, k1_xboole_0), B_314) | k3_xboole_0(A_313, B_314)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_8075])).
% 11.09/4.40  tff(c_8196, plain, (![A_313, B_314]: (r2_hidden('#skF_1'(A_313, B_314, k1_xboole_0), B_314) | k3_xboole_0(A_313, B_314)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_8177])).
% 11.09/4.40  tff(c_1613, plain, (![A_128, B_129, C_130]: (r2_hidden('#skF_1'(A_128, B_129, C_130), A_128) | r2_hidden('#skF_2'(A_128, B_129, C_130), C_130) | k3_xboole_0(A_128, B_129)=C_130)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.09/4.40  tff(c_38, plain, (![D_25, A_19, B_20]: (~r2_hidden(D_25, '#skF_6'(A_19, B_20)) | ~r2_hidden(D_25, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.09/4.40  tff(c_20547, plain, (![A_493, B_494, B_495, C_496]: (~r2_hidden('#skF_1'('#skF_6'(A_493, B_494), B_495, C_496), B_494) | ~r2_hidden(A_493, B_494) | r2_hidden('#skF_2'('#skF_6'(A_493, B_494), B_495, C_496), C_496) | k3_xboole_0('#skF_6'(A_493, B_494), B_495)=C_496)), inference(resolution, [status(thm)], [c_1613, c_38])).
% 11.09/4.40  tff(c_20562, plain, (![A_493, B_314]: (~r2_hidden(A_493, B_314) | r2_hidden('#skF_2'('#skF_6'(A_493, B_314), B_314, k1_xboole_0), k1_xboole_0) | k3_xboole_0('#skF_6'(A_493, B_314), B_314)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8196, c_20547])).
% 11.09/4.40  tff(c_20582, plain, (![A_493, B_314]: (~r2_hidden(A_493, B_314) | r2_hidden('#skF_2'('#skF_6'(A_493, B_314), B_314, k1_xboole_0), k1_xboole_0) | k3_xboole_0(B_314, '#skF_6'(A_493, B_314))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20562])).
% 11.09/4.40  tff(c_20591, plain, (![A_497, B_498]: (~r2_hidden(A_497, B_498) | k3_xboole_0(B_498, '#skF_6'(A_497, B_498))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_163, c_20582])).
% 11.09/4.40  tff(c_248, plain, (![B_2, A_1]: (r2_hidden('#skF_5'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_227])).
% 11.09/4.40  tff(c_20994, plain, (![A_497, B_498]: (r2_hidden('#skF_5'('#skF_6'(A_497, B_498), B_498), k1_xboole_0) | r1_xboole_0('#skF_6'(A_497, B_498), B_498) | ~r2_hidden(A_497, B_498))), inference(superposition, [status(thm), theory('equality')], [c_20591, c_248])).
% 11.09/4.40  tff(c_21136, plain, (![A_499, B_500]: (r1_xboole_0('#skF_6'(A_499, B_500), B_500) | ~r2_hidden(A_499, B_500))), inference(negUnitSimplification, [status(thm)], [c_163, c_20994])).
% 11.09/4.40  tff(c_166, plain, (![A_41, B_42]: (r2_hidden('#skF_6'(A_41, B_42), B_42) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.09/4.40  tff(c_42, plain, (![B_27]: (~r1_xboole_0(B_27, '#skF_7') | ~r2_hidden(B_27, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.09/4.40  tff(c_186, plain, (![A_41]: (~r1_xboole_0('#skF_6'(A_41, '#skF_7'), '#skF_7') | ~r2_hidden(A_41, '#skF_7'))), inference(resolution, [status(thm)], [c_166, c_42])).
% 11.09/4.40  tff(c_21161, plain, (![A_501]: (~r2_hidden(A_501, '#skF_7'))), inference(resolution, [status(thm)], [c_21136, c_186])).
% 11.09/4.40  tff(c_21337, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_6208, c_21161])).
% 11.09/4.40  tff(c_21476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_21337])).
% 11.09/4.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.40  
% 11.09/4.40  Inference rules
% 11.09/4.40  ----------------------
% 11.09/4.40  #Ref     : 0
% 11.09/4.40  #Sup     : 5505
% 11.09/4.40  #Fact    : 0
% 11.09/4.40  #Define  : 0
% 11.09/4.40  #Split   : 0
% 11.09/4.40  #Chain   : 0
% 11.09/4.40  #Close   : 0
% 11.09/4.40  
% 11.09/4.40  Ordering : KBO
% 11.09/4.40  
% 11.09/4.40  Simplification rules
% 11.09/4.40  ----------------------
% 11.09/4.40  #Subsume      : 2323
% 11.09/4.40  #Demod        : 1857
% 11.09/4.40  #Tautology    : 995
% 11.09/4.40  #SimpNegUnit  : 132
% 11.09/4.40  #BackRed      : 0
% 11.09/4.40  
% 11.09/4.40  #Partial instantiations: 0
% 11.09/4.40  #Strategies tried      : 1
% 11.09/4.40  
% 11.09/4.40  Timing (in seconds)
% 11.09/4.40  ----------------------
% 11.09/4.40  Preprocessing        : 0.32
% 11.09/4.40  Parsing              : 0.17
% 11.09/4.40  CNF conversion       : 0.03
% 11.09/4.40  Main loop            : 3.29
% 11.09/4.40  Inferencing          : 0.76
% 11.09/4.40  Reduction            : 0.96
% 11.09/4.40  Demodulation         : 0.76
% 11.09/4.40  BG Simplification    : 0.10
% 11.09/4.40  Subsumption          : 1.31
% 11.09/4.40  Abstraction          : 0.11
% 11.09/4.40  MUC search           : 0.00
% 11.09/4.40  Cooper               : 0.00
% 11.09/4.40  Total                : 3.64
% 11.09/4.40  Index Insertion      : 0.00
% 11.09/4.40  Index Deletion       : 0.00
% 11.09/4.40  Index Matching       : 0.00
% 11.09/4.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
