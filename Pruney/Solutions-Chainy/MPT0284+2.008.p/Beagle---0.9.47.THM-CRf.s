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
% DateTime   : Thu Dec  3 09:53:28 EST 2020

% Result     : Theorem 20.14s
% Output     : CNFRefutation 20.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  68 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 (  96 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_36,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),k4_xboole_0(B_9,A_8)) = k5_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_190,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [C_28,A_24] :
      ( r1_tarski(C_28,A_24)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_200,plain,(
    ! [A_24,B_59] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_24),B_59),A_24)
      | r1_tarski(k1_zfmisc_1(A_24),B_59) ) ),
    inference(resolution,[status(thm)],[c_190,c_24])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [C_28,A_24] :
      ( r2_hidden(C_28,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_175,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden('#skF_1'(A_54,B_55),B_55)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_31625,plain,(
    ! [A_562,A_563] :
      ( r1_tarski(A_562,k1_zfmisc_1(A_563))
      | ~ r1_tarski('#skF_1'(A_562,k1_zfmisc_1(A_563)),A_563) ) ),
    inference(resolution,[status(thm)],[c_26,c_175])).

tff(c_57588,plain,(
    ! [A_877,C_878,B_879] :
      ( r1_tarski(A_877,k1_zfmisc_1(k2_xboole_0(C_878,B_879)))
      | ~ r1_tarski('#skF_1'(A_877,k1_zfmisc_1(k2_xboole_0(C_878,B_879))),B_879) ) ),
    inference(resolution,[status(thm)],[c_14,c_31625])).

tff(c_57814,plain,(
    ! [A_880,C_881] : r1_tarski(k1_zfmisc_1(A_880),k1_zfmisc_1(k2_xboole_0(C_881,A_880))) ),
    inference(resolution,[status(thm)],[c_200,c_57588])).

tff(c_57974,plain,(
    ! [B_9,A_8] : r1_tarski(k1_zfmisc_1(k4_xboole_0(B_9,A_8)),k1_zfmisc_1(k5_xboole_0(A_8,B_9))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57814])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,k2_xboole_0(C_46,B_47))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    ! [A_45,A_1,B_2] :
      ( r1_tarski(A_45,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_45,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_4448,plain,(
    ! [A_164,A_165] :
      ( r1_tarski(A_164,k1_zfmisc_1(A_165))
      | ~ r1_tarski('#skF_1'(A_164,k1_zfmisc_1(A_165)),A_165) ) ),
    inference(resolution,[status(thm)],[c_26,c_175])).

tff(c_25639,plain,(
    ! [A_462,A_463,B_464] :
      ( r1_tarski(A_462,k1_zfmisc_1(k2_xboole_0(A_463,B_464)))
      | ~ r1_tarski('#skF_1'(A_462,k1_zfmisc_1(k2_xboole_0(A_463,B_464))),A_463) ) ),
    inference(resolution,[status(thm)],[c_123,c_4448])).

tff(c_25808,plain,(
    ! [A_465,B_466] : r1_tarski(k1_zfmisc_1(A_465),k1_zfmisc_1(k2_xboole_0(A_465,B_466))) ),
    inference(resolution,[status(thm)],[c_200,c_25639])).

tff(c_25920,plain,(
    ! [A_8,B_9] : r1_tarski(k1_zfmisc_1(k4_xboole_0(A_8,B_9)),k1_zfmisc_1(k5_xboole_0(A_8,B_9))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_25808])).

tff(c_376,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(k2_xboole_0(A_71,C_72),B_73)
      | ~ r1_tarski(C_72,B_73)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4'))),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_404,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_376,c_38])).

tff(c_515,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_29161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25920,c_515])).

tff(c_29162,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_66275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57974,c_29162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:34:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.14/10.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.20/10.32  
% 20.20/10.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.20/10.32  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 20.20/10.32  
% 20.20/10.32  %Foreground sorts:
% 20.20/10.32  
% 20.20/10.32  
% 20.20/10.32  %Background operators:
% 20.20/10.32  
% 20.20/10.32  
% 20.20/10.32  %Foreground operators:
% 20.20/10.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.20/10.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.20/10.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.20/10.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.20/10.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.20/10.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.20/10.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.20/10.32  tff('#skF_5', type, '#skF_5': $i).
% 20.20/10.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.20/10.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.20/10.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.20/10.32  tff('#skF_4', type, '#skF_4': $i).
% 20.20/10.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.20/10.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.20/10.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.20/10.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.20/10.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.20/10.32  
% 20.20/10.33  tff(f_36, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 20.20/10.33  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 20.20/10.33  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 20.20/10.33  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 20.20/10.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 20.20/10.33  tff(f_56, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 20.20/10.33  tff(f_68, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 20.20/10.33  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), k4_xboole_0(B_9, A_8))=k5_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.20/10.33  tff(c_190, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), A_58) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.20/10.33  tff(c_24, plain, (![C_28, A_24]: (r1_tarski(C_28, A_24) | ~r2_hidden(C_28, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.20/10.33  tff(c_200, plain, (![A_24, B_59]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_24), B_59), A_24) | r1_tarski(k1_zfmisc_1(A_24), B_59))), inference(resolution, [status(thm)], [c_190, c_24])).
% 20.20/10.33  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.20/10.33  tff(c_26, plain, (![C_28, A_24]: (r2_hidden(C_28, k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.20/10.33  tff(c_175, plain, (![A_54, B_55]: (~r2_hidden('#skF_1'(A_54, B_55), B_55) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.20/10.33  tff(c_31625, plain, (![A_562, A_563]: (r1_tarski(A_562, k1_zfmisc_1(A_563)) | ~r1_tarski('#skF_1'(A_562, k1_zfmisc_1(A_563)), A_563))), inference(resolution, [status(thm)], [c_26, c_175])).
% 20.20/10.33  tff(c_57588, plain, (![A_877, C_878, B_879]: (r1_tarski(A_877, k1_zfmisc_1(k2_xboole_0(C_878, B_879))) | ~r1_tarski('#skF_1'(A_877, k1_zfmisc_1(k2_xboole_0(C_878, B_879))), B_879))), inference(resolution, [status(thm)], [c_14, c_31625])).
% 20.20/10.33  tff(c_57814, plain, (![A_880, C_881]: (r1_tarski(k1_zfmisc_1(A_880), k1_zfmisc_1(k2_xboole_0(C_881, A_880))))), inference(resolution, [status(thm)], [c_200, c_57588])).
% 20.20/10.33  tff(c_57974, plain, (![B_9, A_8]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(B_9, A_8)), k1_zfmisc_1(k5_xboole_0(A_8, B_9))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57814])).
% 20.20/10.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.20/10.33  tff(c_114, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, k2_xboole_0(C_46, B_47)) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.20/10.33  tff(c_123, plain, (![A_45, A_1, B_2]: (r1_tarski(A_45, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_45, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_114])).
% 20.20/10.33  tff(c_4448, plain, (![A_164, A_165]: (r1_tarski(A_164, k1_zfmisc_1(A_165)) | ~r1_tarski('#skF_1'(A_164, k1_zfmisc_1(A_165)), A_165))), inference(resolution, [status(thm)], [c_26, c_175])).
% 20.20/10.33  tff(c_25639, plain, (![A_462, A_463, B_464]: (r1_tarski(A_462, k1_zfmisc_1(k2_xboole_0(A_463, B_464))) | ~r1_tarski('#skF_1'(A_462, k1_zfmisc_1(k2_xboole_0(A_463, B_464))), A_463))), inference(resolution, [status(thm)], [c_123, c_4448])).
% 20.20/10.33  tff(c_25808, plain, (![A_465, B_466]: (r1_tarski(k1_zfmisc_1(A_465), k1_zfmisc_1(k2_xboole_0(A_465, B_466))))), inference(resolution, [status(thm)], [c_200, c_25639])).
% 20.20/10.33  tff(c_25920, plain, (![A_8, B_9]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(A_8, B_9)), k1_zfmisc_1(k5_xboole_0(A_8, B_9))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_25808])).
% 20.20/10.33  tff(c_376, plain, (![A_71, C_72, B_73]: (r1_tarski(k2_xboole_0(A_71, C_72), B_73) | ~r1_tarski(C_72, B_73) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.20/10.33  tff(c_38, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4'))), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.20/10.33  tff(c_404, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_376, c_38])).
% 20.20/10.33  tff(c_515, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_404])).
% 20.20/10.33  tff(c_29161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25920, c_515])).
% 20.20/10.33  tff(c_29162, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_404])).
% 20.20/10.33  tff(c_66275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57974, c_29162])).
% 20.20/10.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.20/10.33  
% 20.20/10.33  Inference rules
% 20.20/10.33  ----------------------
% 20.20/10.33  #Ref     : 0
% 20.20/10.33  #Sup     : 16918
% 20.20/10.33  #Fact    : 0
% 20.20/10.33  #Define  : 0
% 20.20/10.33  #Split   : 1
% 20.20/10.33  #Chain   : 0
% 20.20/10.33  #Close   : 0
% 20.20/10.33  
% 20.20/10.33  Ordering : KBO
% 20.20/10.33  
% 20.20/10.33  Simplification rules
% 20.20/10.33  ----------------------
% 20.20/10.33  #Subsume      : 1195
% 20.20/10.33  #Demod        : 12588
% 20.20/10.33  #Tautology    : 7112
% 20.20/10.33  #SimpNegUnit  : 0
% 20.20/10.33  #BackRed      : 5
% 20.20/10.33  
% 20.20/10.33  #Partial instantiations: 0
% 20.20/10.33  #Strategies tried      : 1
% 20.20/10.33  
% 20.20/10.33  Timing (in seconds)
% 20.20/10.33  ----------------------
% 20.20/10.34  Preprocessing        : 0.32
% 20.20/10.34  Parsing              : 0.17
% 20.20/10.34  CNF conversion       : 0.02
% 20.20/10.34  Main loop            : 9.22
% 20.20/10.34  Inferencing          : 1.20
% 20.20/10.34  Reduction            : 5.12
% 20.20/10.34  Demodulation         : 4.62
% 20.20/10.34  BG Simplification    : 0.17
% 20.20/10.34  Subsumption          : 2.21
% 20.20/10.34  Abstraction          : 0.25
% 20.20/10.34  MUC search           : 0.00
% 20.20/10.34  Cooper               : 0.00
% 20.20/10.34  Total                : 9.56
% 20.20/10.34  Index Insertion      : 0.00
% 20.20/10.34  Index Deletion       : 0.00
% 20.20/10.34  Index Matching       : 0.00
% 20.20/10.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
