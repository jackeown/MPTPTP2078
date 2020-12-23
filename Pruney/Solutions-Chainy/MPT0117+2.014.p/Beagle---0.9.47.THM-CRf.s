%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:31 EST 2020

% Result     : Theorem 20.99s
% Output     : CNFRefutation 21.09s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 160 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 397 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_1'(A_11,B_12),B_12)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_26])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(A_17,B_18)
      | r2_hidden(A_17,C_19)
      | ~ r2_hidden(A_17,k5_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_143,plain,(
    ! [B_43,C_44,B_45] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_43,C_44),B_45),B_43)
      | r2_hidden('#skF_1'(k5_xboole_0(B_43,C_44),B_45),C_44)
      | r1_tarski(k5_xboole_0(B_43,C_44),B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2462,plain,(
    ! [B_212,C_213,B_214,B_215] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_212,C_213),B_214),B_215)
      | ~ r1_tarski(C_213,B_215)
      | r2_hidden('#skF_1'(k5_xboole_0(B_212,C_213),B_214),B_212)
      | r1_tarski(k5_xboole_0(B_212,C_213),B_214) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_50248,plain,(
    ! [B_826,B_823,B_822,B_824,C_825] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_824,C_825),B_826),B_823)
      | ~ r1_tarski(B_822,B_823)
      | ~ r1_tarski(C_825,B_822)
      | r2_hidden('#skF_1'(k5_xboole_0(B_824,C_825),B_826),B_824)
      | r1_tarski(k5_xboole_0(B_824,C_825),B_826) ) ),
    inference(resolution,[status(thm)],[c_2462,c_2])).

tff(c_53037,plain,(
    ! [B_846,C_847,B_848] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_846,C_847),B_848),'#skF_3')
      | ~ r1_tarski(C_847,'#skF_4')
      | r2_hidden('#skF_1'(k5_xboole_0(B_846,C_847),B_848),B_846)
      | r1_tarski(k5_xboole_0(B_846,C_847),B_848) ) ),
    inference(resolution,[status(thm)],[c_22,c_50248])).

tff(c_42,plain,(
    ! [B_18,C_19,B_2] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_18,C_19),B_2),B_18)
      | r2_hidden('#skF_1'(k5_xboole_0(B_18,C_19),B_2),C_19)
      | r1_tarski(k5_xboole_0(B_18,C_19),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_141,plain,(
    ! [B_18,B_2] :
      ( r1_tarski(k5_xboole_0(B_18,B_18),B_2)
      | r2_hidden('#skF_1'(k5_xboole_0(B_18,B_18),B_2),B_18) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_42])).

tff(c_56,plain,(
    ! [A_23,C_24,B_25] :
      ( ~ r2_hidden(A_23,C_24)
      | ~ r2_hidden(A_23,B_25)
      | ~ r2_hidden(A_23,k5_xboole_0(B_25,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_654,plain,(
    ! [B_98,C_99,B_100] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_98,C_99),B_100),C_99)
      | ~ r2_hidden('#skF_1'(k5_xboole_0(B_98,C_99),B_100),B_98)
      | r1_tarski(k5_xboole_0(B_98,C_99),B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_710,plain,(
    ! [B_101,B_102] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_101,B_101),B_102),B_101)
      | r1_tarski(k5_xboole_0(B_101,B_101),B_102) ) ),
    inference(resolution,[status(thm)],[c_141,c_654])).

tff(c_777,plain,(
    ! [B_18,B_2] : r1_tarski(k5_xboole_0(B_18,B_18),B_2) ),
    inference(resolution,[status(thm)],[c_141,c_710])).

tff(c_43,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(A_20,B_21)
      | ~ r2_hidden(A_20,C_22)
      | r2_hidden(A_20,k5_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_448,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k5_xboole_0(B_82,C_83))
      | r2_hidden('#skF_1'(A_81,k5_xboole_0(B_82,C_83)),B_82)
      | ~ r2_hidden('#skF_1'(A_81,k5_xboole_0(B_82,C_83)),C_83) ) ),
    inference(resolution,[status(thm)],[c_43,c_4])).

tff(c_525,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,k5_xboole_0(B_86,A_85)),B_86)
      | r1_tarski(A_85,k5_xboole_0(B_86,A_85)) ) ),
    inference(resolution,[status(thm)],[c_6,c_448])).

tff(c_979,plain,(
    ! [A_120,B_121,B_122] :
      ( r2_hidden('#skF_1'(A_120,k5_xboole_0(B_121,A_120)),B_122)
      | ~ r1_tarski(B_121,B_122)
      | r1_tarski(A_120,k5_xboole_0(B_121,A_120)) ) ),
    inference(resolution,[status(thm)],[c_525,c_2])).

tff(c_1018,plain,(
    ! [B_123,A_124] :
      ( ~ r1_tarski(B_123,k5_xboole_0(B_123,A_124))
      | r1_tarski(A_124,k5_xboole_0(B_123,A_124)) ) ),
    inference(resolution,[status(thm)],[c_979,c_4])).

tff(c_1022,plain,(
    ! [A_124,B_18] : r1_tarski(A_124,k5_xboole_0(k5_xboole_0(B_18,B_18),A_124)) ),
    inference(resolution,[status(thm)],[c_777,c_1018])).

tff(c_175,plain,(
    ! [B_43,C_44] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_43,C_44),B_43),C_44)
      | r1_tarski(k5_xboole_0(B_43,C_44),B_43) ) ),
    inference(resolution,[status(thm)],[c_143,c_4])).

tff(c_32,plain,(
    ! [C_13,B_14,A_15] :
      ( r2_hidden(C_13,B_14)
      | ~ r2_hidden(C_13,A_15)
      | ~ r1_tarski(A_15,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_29,B_30,B_31] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_31)
      | ~ r1_tarski(A_29,B_31)
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( ~ r2_hidden(A_6,C_8)
      | ~ r2_hidden(A_6,B_7)
      | ~ r2_hidden(A_6,k5_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1356,plain,(
    ! [A_148,B_149,C_150,B_151] :
      ( ~ r2_hidden('#skF_1'(A_148,B_149),C_150)
      | ~ r2_hidden('#skF_1'(A_148,B_149),B_151)
      | ~ r1_tarski(A_148,k5_xboole_0(B_151,C_150))
      | r1_tarski(A_148,B_149) ) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_1568,plain,(
    ! [A_160,B_161,B_162] :
      ( ~ r2_hidden('#skF_1'(A_160,B_161),B_162)
      | ~ r1_tarski(A_160,k5_xboole_0(B_162,A_160))
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_6,c_1356])).

tff(c_7769,plain,(
    ! [B_364,C_365] :
      ( ~ r1_tarski(k5_xboole_0(B_364,C_365),k5_xboole_0(C_365,k5_xboole_0(B_364,C_365)))
      | r1_tarski(k5_xboole_0(B_364,C_365),B_364) ) ),
    inference(resolution,[status(thm)],[c_175,c_1568])).

tff(c_7876,plain,(
    ! [B_366,B_367] : r1_tarski(k5_xboole_0(B_366,k5_xboole_0(B_367,B_367)),B_366) ),
    inference(resolution,[status(thm)],[c_1022,c_7769])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_263,plain,(
    ! [A_56,B_57,B_58,B_59] :
      ( r2_hidden('#skF_1'(A_56,B_57),B_58)
      | ~ r1_tarski(B_59,B_58)
      | ~ r1_tarski(A_56,B_59)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_342,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),'#skF_3')
      | ~ r1_tarski(A_66,'#skF_2')
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_24,c_263])).

tff(c_354,plain,(
    ! [A_66] :
      ( ~ r1_tarski(A_66,'#skF_2')
      | r1_tarski(A_66,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_342,c_4])).

tff(c_7943,plain,(
    ! [B_368] : r1_tarski(k5_xboole_0('#skF_2',k5_xboole_0(B_368,B_368)),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7876,c_354])).

tff(c_66,plain,(
    ! [A_26,C_27,B_28] :
      ( r2_hidden(A_26,C_27)
      | ~ r2_hidden(A_26,B_28)
      | r2_hidden(A_26,k5_xboole_0(B_28,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_26,B_2,B_28,C_27] :
      ( r2_hidden(A_26,B_2)
      | ~ r1_tarski(k5_xboole_0(B_28,C_27),B_2)
      | r2_hidden(A_26,C_27)
      | ~ r2_hidden(A_26,B_28) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_8421,plain,(
    ! [A_378,B_379] :
      ( r2_hidden(A_378,'#skF_3')
      | r2_hidden(A_378,k5_xboole_0(B_379,B_379))
      | ~ r2_hidden(A_378,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_7943,c_81])).

tff(c_1415,plain,(
    ! [A_1,B_2,B_151] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_151)
      | ~ r1_tarski(A_1,k5_xboole_0(B_151,A_1))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1356])).

tff(c_8451,plain,(
    ! [A_1,B_379,B_2] :
      ( ~ r1_tarski(A_1,k5_xboole_0(k5_xboole_0(B_379,B_379),A_1))
      | r1_tarski(A_1,B_2)
      | r2_hidden('#skF_1'(A_1,B_2),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_1,B_2),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8421,c_1415])).

tff(c_8493,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | r2_hidden('#skF_1'(A_1,B_2),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_1,B_2),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_8451])).

tff(c_71053,plain,(
    ! [C_964,B_965] :
      ( r2_hidden('#skF_1'(k5_xboole_0('#skF_2',C_964),B_965),'#skF_3')
      | ~ r1_tarski(C_964,'#skF_4')
      | r1_tarski(k5_xboole_0('#skF_2',C_964),B_965) ) ),
    inference(resolution,[status(thm)],[c_53037,c_8493])).

tff(c_71157,plain,(
    ! [C_966] :
      ( ~ r1_tarski(C_966,'#skF_4')
      | r1_tarski(k5_xboole_0('#skF_2',C_966),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_71053,c_4])).

tff(c_20,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71195,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_71157,c_20])).

tff(c_71214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_71195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.99/13.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.99/13.20  
% 20.99/13.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.99/13.20  %$ r2_hidden > r1_tarski > k5_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 20.99/13.20  
% 20.99/13.20  %Foreground sorts:
% 20.99/13.20  
% 20.99/13.20  
% 20.99/13.20  %Background operators:
% 20.99/13.20  
% 20.99/13.20  
% 20.99/13.20  %Foreground operators:
% 20.99/13.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.99/13.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.99/13.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.99/13.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.99/13.20  tff('#skF_2', type, '#skF_2': $i).
% 20.99/13.20  tff('#skF_3', type, '#skF_3': $i).
% 20.99/13.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.99/13.20  tff('#skF_4', type, '#skF_4': $i).
% 20.99/13.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.99/13.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.99/13.20  
% 21.09/13.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 21.09/13.21  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 21.09/13.21  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 21.09/13.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.09/13.21  tff(c_26, plain, (![A_11, B_12]: (~r2_hidden('#skF_1'(A_11, B_12), B_12) | r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.09/13.21  tff(c_31, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_26])).
% 21.09/13.21  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.09/13.21  tff(c_37, plain, (![A_17, B_18, C_19]: (r2_hidden(A_17, B_18) | r2_hidden(A_17, C_19) | ~r2_hidden(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.09/13.21  tff(c_143, plain, (![B_43, C_44, B_45]: (r2_hidden('#skF_1'(k5_xboole_0(B_43, C_44), B_45), B_43) | r2_hidden('#skF_1'(k5_xboole_0(B_43, C_44), B_45), C_44) | r1_tarski(k5_xboole_0(B_43, C_44), B_45))), inference(resolution, [status(thm)], [c_6, c_37])).
% 21.09/13.21  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.09/13.21  tff(c_2462, plain, (![B_212, C_213, B_214, B_215]: (r2_hidden('#skF_1'(k5_xboole_0(B_212, C_213), B_214), B_215) | ~r1_tarski(C_213, B_215) | r2_hidden('#skF_1'(k5_xboole_0(B_212, C_213), B_214), B_212) | r1_tarski(k5_xboole_0(B_212, C_213), B_214))), inference(resolution, [status(thm)], [c_143, c_2])).
% 21.09/13.21  tff(c_50248, plain, (![B_826, B_823, B_822, B_824, C_825]: (r2_hidden('#skF_1'(k5_xboole_0(B_824, C_825), B_826), B_823) | ~r1_tarski(B_822, B_823) | ~r1_tarski(C_825, B_822) | r2_hidden('#skF_1'(k5_xboole_0(B_824, C_825), B_826), B_824) | r1_tarski(k5_xboole_0(B_824, C_825), B_826))), inference(resolution, [status(thm)], [c_2462, c_2])).
% 21.09/13.21  tff(c_53037, plain, (![B_846, C_847, B_848]: (r2_hidden('#skF_1'(k5_xboole_0(B_846, C_847), B_848), '#skF_3') | ~r1_tarski(C_847, '#skF_4') | r2_hidden('#skF_1'(k5_xboole_0(B_846, C_847), B_848), B_846) | r1_tarski(k5_xboole_0(B_846, C_847), B_848))), inference(resolution, [status(thm)], [c_22, c_50248])).
% 21.09/13.21  tff(c_42, plain, (![B_18, C_19, B_2]: (r2_hidden('#skF_1'(k5_xboole_0(B_18, C_19), B_2), B_18) | r2_hidden('#skF_1'(k5_xboole_0(B_18, C_19), B_2), C_19) | r1_tarski(k5_xboole_0(B_18, C_19), B_2))), inference(resolution, [status(thm)], [c_6, c_37])).
% 21.09/13.21  tff(c_141, plain, (![B_18, B_2]: (r1_tarski(k5_xboole_0(B_18, B_18), B_2) | r2_hidden('#skF_1'(k5_xboole_0(B_18, B_18), B_2), B_18))), inference(factorization, [status(thm), theory('equality')], [c_42])).
% 21.09/13.21  tff(c_56, plain, (![A_23, C_24, B_25]: (~r2_hidden(A_23, C_24) | ~r2_hidden(A_23, B_25) | ~r2_hidden(A_23, k5_xboole_0(B_25, C_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.09/13.21  tff(c_654, plain, (![B_98, C_99, B_100]: (~r2_hidden('#skF_1'(k5_xboole_0(B_98, C_99), B_100), C_99) | ~r2_hidden('#skF_1'(k5_xboole_0(B_98, C_99), B_100), B_98) | r1_tarski(k5_xboole_0(B_98, C_99), B_100))), inference(resolution, [status(thm)], [c_6, c_56])).
% 21.09/13.21  tff(c_710, plain, (![B_101, B_102]: (~r2_hidden('#skF_1'(k5_xboole_0(B_101, B_101), B_102), B_101) | r1_tarski(k5_xboole_0(B_101, B_101), B_102))), inference(resolution, [status(thm)], [c_141, c_654])).
% 21.09/13.21  tff(c_777, plain, (![B_18, B_2]: (r1_tarski(k5_xboole_0(B_18, B_18), B_2))), inference(resolution, [status(thm)], [c_141, c_710])).
% 21.09/13.21  tff(c_43, plain, (![A_20, B_21, C_22]: (r2_hidden(A_20, B_21) | ~r2_hidden(A_20, C_22) | r2_hidden(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.09/13.21  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.09/13.21  tff(c_448, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k5_xboole_0(B_82, C_83)) | r2_hidden('#skF_1'(A_81, k5_xboole_0(B_82, C_83)), B_82) | ~r2_hidden('#skF_1'(A_81, k5_xboole_0(B_82, C_83)), C_83))), inference(resolution, [status(thm)], [c_43, c_4])).
% 21.09/13.21  tff(c_525, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, k5_xboole_0(B_86, A_85)), B_86) | r1_tarski(A_85, k5_xboole_0(B_86, A_85)))), inference(resolution, [status(thm)], [c_6, c_448])).
% 21.09/13.21  tff(c_979, plain, (![A_120, B_121, B_122]: (r2_hidden('#skF_1'(A_120, k5_xboole_0(B_121, A_120)), B_122) | ~r1_tarski(B_121, B_122) | r1_tarski(A_120, k5_xboole_0(B_121, A_120)))), inference(resolution, [status(thm)], [c_525, c_2])).
% 21.09/13.21  tff(c_1018, plain, (![B_123, A_124]: (~r1_tarski(B_123, k5_xboole_0(B_123, A_124)) | r1_tarski(A_124, k5_xboole_0(B_123, A_124)))), inference(resolution, [status(thm)], [c_979, c_4])).
% 21.09/13.21  tff(c_1022, plain, (![A_124, B_18]: (r1_tarski(A_124, k5_xboole_0(k5_xboole_0(B_18, B_18), A_124)))), inference(resolution, [status(thm)], [c_777, c_1018])).
% 21.09/13.21  tff(c_175, plain, (![B_43, C_44]: (r2_hidden('#skF_1'(k5_xboole_0(B_43, C_44), B_43), C_44) | r1_tarski(k5_xboole_0(B_43, C_44), B_43))), inference(resolution, [status(thm)], [c_143, c_4])).
% 21.09/13.21  tff(c_32, plain, (![C_13, B_14, A_15]: (r2_hidden(C_13, B_14) | ~r2_hidden(C_13, A_15) | ~r1_tarski(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.09/13.21  tff(c_83, plain, (![A_29, B_30, B_31]: (r2_hidden('#skF_1'(A_29, B_30), B_31) | ~r1_tarski(A_29, B_31) | r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_6, c_32])).
% 21.09/13.21  tff(c_8, plain, (![A_6, C_8, B_7]: (~r2_hidden(A_6, C_8) | ~r2_hidden(A_6, B_7) | ~r2_hidden(A_6, k5_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.09/13.21  tff(c_1356, plain, (![A_148, B_149, C_150, B_151]: (~r2_hidden('#skF_1'(A_148, B_149), C_150) | ~r2_hidden('#skF_1'(A_148, B_149), B_151) | ~r1_tarski(A_148, k5_xboole_0(B_151, C_150)) | r1_tarski(A_148, B_149))), inference(resolution, [status(thm)], [c_83, c_8])).
% 21.09/13.21  tff(c_1568, plain, (![A_160, B_161, B_162]: (~r2_hidden('#skF_1'(A_160, B_161), B_162) | ~r1_tarski(A_160, k5_xboole_0(B_162, A_160)) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_6, c_1356])).
% 21.09/13.21  tff(c_7769, plain, (![B_364, C_365]: (~r1_tarski(k5_xboole_0(B_364, C_365), k5_xboole_0(C_365, k5_xboole_0(B_364, C_365))) | r1_tarski(k5_xboole_0(B_364, C_365), B_364))), inference(resolution, [status(thm)], [c_175, c_1568])).
% 21.09/13.21  tff(c_7876, plain, (![B_366, B_367]: (r1_tarski(k5_xboole_0(B_366, k5_xboole_0(B_367, B_367)), B_366))), inference(resolution, [status(thm)], [c_1022, c_7769])).
% 21.09/13.21  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.09/13.21  tff(c_263, plain, (![A_56, B_57, B_58, B_59]: (r2_hidden('#skF_1'(A_56, B_57), B_58) | ~r1_tarski(B_59, B_58) | ~r1_tarski(A_56, B_59) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_83, c_2])).
% 21.09/13.21  tff(c_342, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), '#skF_3') | ~r1_tarski(A_66, '#skF_2') | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_24, c_263])).
% 21.09/13.21  tff(c_354, plain, (![A_66]: (~r1_tarski(A_66, '#skF_2') | r1_tarski(A_66, '#skF_3'))), inference(resolution, [status(thm)], [c_342, c_4])).
% 21.09/13.21  tff(c_7943, plain, (![B_368]: (r1_tarski(k5_xboole_0('#skF_2', k5_xboole_0(B_368, B_368)), '#skF_3'))), inference(resolution, [status(thm)], [c_7876, c_354])).
% 21.09/13.21  tff(c_66, plain, (![A_26, C_27, B_28]: (r2_hidden(A_26, C_27) | ~r2_hidden(A_26, B_28) | r2_hidden(A_26, k5_xboole_0(B_28, C_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.09/13.21  tff(c_81, plain, (![A_26, B_2, B_28, C_27]: (r2_hidden(A_26, B_2) | ~r1_tarski(k5_xboole_0(B_28, C_27), B_2) | r2_hidden(A_26, C_27) | ~r2_hidden(A_26, B_28))), inference(resolution, [status(thm)], [c_66, c_2])).
% 21.09/13.21  tff(c_8421, plain, (![A_378, B_379]: (r2_hidden(A_378, '#skF_3') | r2_hidden(A_378, k5_xboole_0(B_379, B_379)) | ~r2_hidden(A_378, '#skF_2'))), inference(resolution, [status(thm)], [c_7943, c_81])).
% 21.09/13.21  tff(c_1415, plain, (![A_1, B_2, B_151]: (~r2_hidden('#skF_1'(A_1, B_2), B_151) | ~r1_tarski(A_1, k5_xboole_0(B_151, A_1)) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_1356])).
% 21.09/13.21  tff(c_8451, plain, (![A_1, B_379, B_2]: (~r1_tarski(A_1, k5_xboole_0(k5_xboole_0(B_379, B_379), A_1)) | r1_tarski(A_1, B_2) | r2_hidden('#skF_1'(A_1, B_2), '#skF_3') | ~r2_hidden('#skF_1'(A_1, B_2), '#skF_2'))), inference(resolution, [status(thm)], [c_8421, c_1415])).
% 21.09/13.21  tff(c_8493, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | r2_hidden('#skF_1'(A_1, B_2), '#skF_3') | ~r2_hidden('#skF_1'(A_1, B_2), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_8451])).
% 21.09/13.21  tff(c_71053, plain, (![C_964, B_965]: (r2_hidden('#skF_1'(k5_xboole_0('#skF_2', C_964), B_965), '#skF_3') | ~r1_tarski(C_964, '#skF_4') | r1_tarski(k5_xboole_0('#skF_2', C_964), B_965))), inference(resolution, [status(thm)], [c_53037, c_8493])).
% 21.09/13.21  tff(c_71157, plain, (![C_966]: (~r1_tarski(C_966, '#skF_4') | r1_tarski(k5_xboole_0('#skF_2', C_966), '#skF_3'))), inference(resolution, [status(thm)], [c_71053, c_4])).
% 21.09/13.21  tff(c_20, plain, (~r1_tarski(k5_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.09/13.21  tff(c_71195, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_71157, c_20])).
% 21.09/13.21  tff(c_71214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_71195])).
% 21.09/13.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.09/13.21  
% 21.09/13.21  Inference rules
% 21.09/13.21  ----------------------
% 21.09/13.21  #Ref     : 0
% 21.09/13.21  #Sup     : 15460
% 21.09/13.21  #Fact    : 46
% 21.09/13.21  #Define  : 0
% 21.09/13.21  #Split   : 12
% 21.09/13.21  #Chain   : 0
% 21.09/13.21  #Close   : 0
% 21.09/13.21  
% 21.09/13.21  Ordering : KBO
% 21.09/13.21  
% 21.09/13.21  Simplification rules
% 21.09/13.21  ----------------------
% 21.09/13.21  #Subsume      : 8721
% 21.09/13.21  #Demod        : 6639
% 21.09/13.21  #Tautology    : 1642
% 21.09/13.21  #SimpNegUnit  : 774
% 21.09/13.21  #BackRed      : 0
% 21.09/13.21  
% 21.09/13.21  #Partial instantiations: 0
% 21.09/13.21  #Strategies tried      : 1
% 21.09/13.21  
% 21.09/13.21  Timing (in seconds)
% 21.09/13.21  ----------------------
% 21.09/13.22  Preprocessing        : 0.24
% 21.09/13.22  Parsing              : 0.13
% 21.09/13.22  CNF conversion       : 0.02
% 21.09/13.22  Main loop            : 12.20
% 21.09/13.22  Inferencing          : 1.46
% 21.09/13.22  Reduction            : 2.88
% 21.09/13.22  Demodulation         : 2.09
% 21.09/13.22  BG Simplification    : 0.12
% 21.09/13.22  Subsumption          : 7.28
% 21.09/13.22  Abstraction          : 0.22
% 21.09/13.22  MUC search           : 0.00
% 21.09/13.22  Cooper               : 0.00
% 21.09/13.22  Total                : 12.48
% 21.09/13.22  Index Insertion      : 0.00
% 21.09/13.22  Index Deletion       : 0.00
% 21.09/13.22  Index Matching       : 0.00
% 21.09/13.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
