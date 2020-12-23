%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:10 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 129 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 224 expanded)
%              Number of equality atoms :    9 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(c_44,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_1393,plain,(
    ! [A_145,C_146,B_147] :
      ( ~ r1_xboole_0(A_145,C_146)
      | ~ r1_xboole_0(A_145,B_147)
      | r1_xboole_0(A_145,k2_xboole_0(B_147,C_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4583,plain,(
    ! [B_286,C_287,A_288] :
      ( r1_xboole_0(k2_xboole_0(B_286,C_287),A_288)
      | ~ r1_xboole_0(A_288,C_287)
      | ~ r1_xboole_0(A_288,B_286) ) ),
    inference(resolution,[status(thm)],[c_1393,c_4])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4616,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4583,c_42])).

tff(c_4629,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4616])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_130,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = A_50
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1989,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(k1_tarski(A_187),B_188) = k1_tarski(A_187)
      | r2_hidden(A_187,B_188) ) ),
    inference(resolution,[status(thm)],[c_40,c_130])).

tff(c_16,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,k4_xboole_0(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11079,plain,(
    ! [A_446,B_447,A_448] :
      ( r1_xboole_0(A_446,B_447)
      | ~ r1_tarski(A_446,k1_tarski(A_448))
      | r2_hidden(A_448,B_447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1989,c_16])).

tff(c_11362,plain,(
    ! [B_452] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_452)
      | r2_hidden('#skF_6',B_452) ) ),
    inference(resolution,[status(thm)],[c_49,c_11079])).

tff(c_334,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [A_26,B_27] : r1_xboole_0(k4_xboole_0(A_26,B_27),B_27) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_65,plain,(
    ! [B_27,A_26] : r1_xboole_0(B_27,k4_xboole_0(A_26,B_27)) ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_151,plain,(
    ! [B_27,A_26] : k4_xboole_0(B_27,k4_xboole_0(A_26,B_27)) = B_27 ),
    inference(resolution,[status(thm)],[c_65,c_130])).

tff(c_350,plain,(
    ! [B_81] : k3_xboole_0(B_81,B_81) = B_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_151])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_823,plain,(
    ! [A_105,B_106,C_107] :
      ( ~ r1_xboole_0(A_105,B_106)
      | ~ r2_hidden(C_107,k3_xboole_0(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1513,plain,(
    ! [A_158,B_159,B_160] :
      ( ~ r1_xboole_0(A_158,B_159)
      | r1_xboole_0(k3_xboole_0(A_158,B_159),B_160) ) ),
    inference(resolution,[status(thm)],[c_10,c_823])).

tff(c_1537,plain,(
    ! [B_81,B_160] :
      ( ~ r1_xboole_0(B_81,B_81)
      | r1_xboole_0(B_81,B_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1513])).

tff(c_11430,plain,(
    ! [B_160] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_160)
      | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_11362,c_1537])).

tff(c_12592,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11430])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | r1_xboole_0(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1018,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r1_xboole_0(A_121,B_122)
      | ~ r2_hidden(C_123,B_122)
      | ~ r2_hidden(C_123,A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1081,plain,(
    ! [C_123,B_24,C_25,A_23] :
      ( ~ r2_hidden(C_123,k3_xboole_0(B_24,C_25))
      | ~ r2_hidden(C_123,A_23)
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_28,c_1018])).

tff(c_12638,plain,(
    ! [A_483] :
      ( ~ r2_hidden('#skF_6',A_483)
      | ~ r1_xboole_0(A_483,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12592,c_1081])).

tff(c_12666,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_12638])).

tff(c_12677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12666])).

tff(c_12685,plain,(
    ! [B_484] : r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_484) ),
    inference(splitRight,[status(thm)],[c_11430])).

tff(c_830,plain,(
    ! [B_81,C_107] :
      ( ~ r1_xboole_0(B_81,B_81)
      | ~ r2_hidden(C_107,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_823])).

tff(c_12915,plain,(
    ! [C_490] : ~ r2_hidden(C_490,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12685,c_830])).

tff(c_12927,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_12915])).

tff(c_12942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4629,c_12927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:26:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.96/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.86  
% 7.96/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.96/2.86  
% 7.96/2.86  %Foreground sorts:
% 7.96/2.86  
% 7.96/2.86  
% 7.96/2.86  %Background operators:
% 7.96/2.86  
% 7.96/2.86  
% 7.96/2.86  %Foreground operators:
% 7.96/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.96/2.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.96/2.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.96/2.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.96/2.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.96/2.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.96/2.86  tff('#skF_5', type, '#skF_5': $i).
% 7.96/2.86  tff('#skF_6', type, '#skF_6': $i).
% 7.96/2.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.96/2.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.96/2.86  tff('#skF_3', type, '#skF_3': $i).
% 7.96/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.96/2.86  tff('#skF_4', type, '#skF_4': $i).
% 7.96/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.96/2.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.96/2.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.96/2.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.96/2.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.96/2.86  
% 7.96/2.88  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.96/2.88  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.96/2.88  tff(f_87, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.96/2.88  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.96/2.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.96/2.88  tff(f_108, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.96/2.88  tff(f_99, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.96/2.88  tff(f_69, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.96/2.88  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.96/2.88  tff(f_95, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.96/2.88  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.96/2.88  tff(f_93, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 7.96/2.88  tff(c_44, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.96/2.88  tff(c_60, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.96/2.88  tff(c_66, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_60])).
% 7.96/2.88  tff(c_1393, plain, (![A_145, C_146, B_147]: (~r1_xboole_0(A_145, C_146) | ~r1_xboole_0(A_145, B_147) | r1_xboole_0(A_145, k2_xboole_0(B_147, C_146)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.96/2.88  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.96/2.88  tff(c_4583, plain, (![B_286, C_287, A_288]: (r1_xboole_0(k2_xboole_0(B_286, C_287), A_288) | ~r1_xboole_0(A_288, C_287) | ~r1_xboole_0(A_288, B_286))), inference(resolution, [status(thm)], [c_1393, c_4])).
% 7.96/2.88  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.96/2.88  tff(c_4616, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4583, c_42])).
% 7.96/2.88  tff(c_4629, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4616])).
% 7.96/2.88  tff(c_12, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.96/2.88  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.96/2.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.96/2.88  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.96/2.88  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 7.96/2.88  tff(c_40, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.96/2.88  tff(c_130, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=A_50 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.96/2.88  tff(c_1989, plain, (![A_187, B_188]: (k4_xboole_0(k1_tarski(A_187), B_188)=k1_tarski(A_187) | r2_hidden(A_187, B_188))), inference(resolution, [status(thm)], [c_40, c_130])).
% 7.96/2.88  tff(c_16, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.96/2.88  tff(c_11079, plain, (![A_446, B_447, A_448]: (r1_xboole_0(A_446, B_447) | ~r1_tarski(A_446, k1_tarski(A_448)) | r2_hidden(A_448, B_447))), inference(superposition, [status(thm), theory('equality')], [c_1989, c_16])).
% 7.96/2.88  tff(c_11362, plain, (![B_452]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_452) | r2_hidden('#skF_6', B_452))), inference(resolution, [status(thm)], [c_49, c_11079])).
% 7.96/2.88  tff(c_334, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.96/2.88  tff(c_30, plain, (![A_26, B_27]: (r1_xboole_0(k4_xboole_0(A_26, B_27), B_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.96/2.88  tff(c_65, plain, (![B_27, A_26]: (r1_xboole_0(B_27, k4_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_30, c_60])).
% 7.96/2.88  tff(c_151, plain, (![B_27, A_26]: (k4_xboole_0(B_27, k4_xboole_0(A_26, B_27))=B_27)), inference(resolution, [status(thm)], [c_65, c_130])).
% 7.96/2.88  tff(c_350, plain, (![B_81]: (k3_xboole_0(B_81, B_81)=B_81)), inference(superposition, [status(thm), theory('equality')], [c_334, c_151])).
% 7.96/2.88  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.96/2.88  tff(c_823, plain, (![A_105, B_106, C_107]: (~r1_xboole_0(A_105, B_106) | ~r2_hidden(C_107, k3_xboole_0(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.96/2.88  tff(c_1513, plain, (![A_158, B_159, B_160]: (~r1_xboole_0(A_158, B_159) | r1_xboole_0(k3_xboole_0(A_158, B_159), B_160))), inference(resolution, [status(thm)], [c_10, c_823])).
% 7.96/2.88  tff(c_1537, plain, (![B_81, B_160]: (~r1_xboole_0(B_81, B_81) | r1_xboole_0(B_81, B_160))), inference(superposition, [status(thm), theory('equality')], [c_350, c_1513])).
% 7.96/2.88  tff(c_11430, plain, (![B_160]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_160) | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_11362, c_1537])).
% 7.96/2.88  tff(c_12592, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_11430])).
% 7.96/2.88  tff(c_28, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | r1_xboole_0(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.96/2.88  tff(c_1018, plain, (![A_121, B_122, C_123]: (~r1_xboole_0(A_121, B_122) | ~r2_hidden(C_123, B_122) | ~r2_hidden(C_123, A_121))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.96/2.88  tff(c_1081, plain, (![C_123, B_24, C_25, A_23]: (~r2_hidden(C_123, k3_xboole_0(B_24, C_25)) | ~r2_hidden(C_123, A_23) | ~r1_xboole_0(A_23, B_24))), inference(resolution, [status(thm)], [c_28, c_1018])).
% 7.96/2.88  tff(c_12638, plain, (![A_483]: (~r2_hidden('#skF_6', A_483) | ~r1_xboole_0(A_483, '#skF_4'))), inference(resolution, [status(thm)], [c_12592, c_1081])).
% 7.96/2.88  tff(c_12666, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_12638])).
% 7.96/2.88  tff(c_12677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_12666])).
% 7.96/2.88  tff(c_12685, plain, (![B_484]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_484))), inference(splitRight, [status(thm)], [c_11430])).
% 7.96/2.88  tff(c_830, plain, (![B_81, C_107]: (~r1_xboole_0(B_81, B_81) | ~r2_hidden(C_107, B_81))), inference(superposition, [status(thm), theory('equality')], [c_350, c_823])).
% 7.96/2.88  tff(c_12915, plain, (![C_490]: (~r2_hidden(C_490, k3_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_12685, c_830])).
% 7.96/2.88  tff(c_12927, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_12915])).
% 7.96/2.88  tff(c_12942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4629, c_12927])).
% 7.96/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.88  
% 7.96/2.88  Inference rules
% 7.96/2.88  ----------------------
% 7.96/2.88  #Ref     : 0
% 7.96/2.88  #Sup     : 3167
% 7.96/2.88  #Fact    : 0
% 7.96/2.88  #Define  : 0
% 7.96/2.88  #Split   : 10
% 7.96/2.88  #Chain   : 0
% 7.96/2.88  #Close   : 0
% 7.96/2.88  
% 7.96/2.88  Ordering : KBO
% 7.96/2.88  
% 7.96/2.88  Simplification rules
% 7.96/2.88  ----------------------
% 7.96/2.88  #Subsume      : 615
% 7.96/2.88  #Demod        : 1557
% 7.96/2.88  #Tautology    : 1308
% 7.96/2.88  #SimpNegUnit  : 33
% 7.96/2.88  #BackRed      : 29
% 7.96/2.88  
% 7.96/2.88  #Partial instantiations: 0
% 7.96/2.88  #Strategies tried      : 1
% 7.96/2.88  
% 7.96/2.88  Timing (in seconds)
% 7.96/2.88  ----------------------
% 7.96/2.88  Preprocessing        : 0.33
% 7.96/2.88  Parsing              : 0.18
% 7.96/2.88  CNF conversion       : 0.02
% 7.96/2.88  Main loop            : 1.78
% 7.96/2.88  Inferencing          : 0.48
% 7.96/2.88  Reduction            : 0.69
% 7.96/2.88  Demodulation         : 0.53
% 7.96/2.88  BG Simplification    : 0.05
% 7.96/2.88  Subsumption          : 0.41
% 7.96/2.88  Abstraction          : 0.07
% 7.96/2.88  MUC search           : 0.00
% 7.96/2.88  Cooper               : 0.00
% 7.96/2.88  Total                : 2.15
% 7.96/2.88  Index Insertion      : 0.00
% 7.96/2.88  Index Deletion       : 0.00
% 7.96/2.88  Index Matching       : 0.00
% 7.96/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
