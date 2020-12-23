%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:03 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 133 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 246 expanded)
%              Number of equality atoms :   16 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_79,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_202,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(k1_tarski(A_48),B_49) = B_49
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_220,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_22])).

tff(c_40,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_350,plain,(
    ! [B_64,A_65] :
      ( k1_tarski(B_64) = A_65
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_tarski(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_365,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_350])).

tff(c_398,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( ~ r1_xboole_0(k3_xboole_0(A_15,B_16),B_16)
      | r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_404,plain,
    ( ~ r1_xboole_0(k1_xboole_0,'#skF_2')
    | r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_20])).

tff(c_408,plain,(
    ~ r1_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_30,plain,(
    ! [B_21] : r1_tarski(k1_xboole_0,k1_tarski(B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_259,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_xboole_0(A_57,C_58)
      | ~ r1_xboole_0(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_272,plain,(
    ! [A_60] :
      ( r1_xboole_0(A_60,'#skF_2')
      | ~ r1_tarski(A_60,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_259])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_xboole_0(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_559,plain,(
    ! [A_81,A_82] :
      ( r1_xboole_0(A_81,'#skF_2')
      | ~ r1_tarski(A_81,A_82)
      | ~ r1_tarski(A_82,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_272,c_12])).

tff(c_571,plain,(
    ! [B_21] :
      ( r1_xboole_0(k1_xboole_0,'#skF_2')
      | ~ r1_tarski(k1_tarski(B_21),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_559])).

tff(c_582,plain,(
    ! [B_83] : ~ r1_tarski(k1_tarski(B_83),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_571])).

tff(c_587,plain,(
    ! [A_48] : ~ r2_hidden(A_48,'#skF_3') ),
    inference(resolution,[status(thm)],[c_220,c_582])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_587,c_38])).

tff(c_590,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_612,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_590,c_8])).

tff(c_102,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_624,plain,(
    ! [A_84,C_85,B_86] :
      ( ~ r1_xboole_0(A_84,C_85)
      | ~ r1_xboole_0(A_84,B_86)
      | r1_xboole_0(A_84,k2_xboole_0(B_86,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2095,plain,(
    ! [B_186,C_187,A_188] :
      ( r1_xboole_0(k2_xboole_0(B_186,C_187),A_188)
      | ~ r1_xboole_0(A_188,C_187)
      | ~ r1_xboole_0(A_188,B_186) ) ),
    inference(resolution,[status(thm)],[c_624,c_8])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2115,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_2095,c_34])).

tff(c_2137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_105,c_2115])).

tff(c_2138,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_2139,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_2140,plain,(
    k1_tarski('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_2139])).

tff(c_271,plain,(
    ! [A_57] :
      ( r1_xboole_0(A_57,'#skF_2')
      | ~ r1_tarski(A_57,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_259])).

tff(c_2146,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_2')
    | r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_20])).

tff(c_2158,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2146])).

tff(c_2168,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_271,c_2158])).

tff(c_2173,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_220,c_2168])).

tff(c_2177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2173])).

tff(c_2178,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2146])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2188,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2178,c_4])).

tff(c_2244,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2188,c_2138])).

tff(c_2246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2140,c_2244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.04/1.69  
% 4.04/1.69  %Foreground sorts:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Background operators:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Foreground operators:
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.04/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.04/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.04/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.04/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.04/1.69  
% 4.04/1.70  tff(f_79, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.04/1.70  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.04/1.70  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.04/1.70  tff(f_75, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 4.04/1.70  tff(f_65, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 4.04/1.70  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.04/1.70  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.04/1.70  tff(f_59, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.04/1.70  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.04/1.70  tff(c_202, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), B_49)=B_49 | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.04/1.70  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.04/1.70  tff(c_220, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_202, c_22])).
% 4.04/1.70  tff(c_40, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.70  tff(c_350, plain, (![B_64, A_65]: (k1_tarski(B_64)=A_65 | k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_tarski(B_64)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.70  tff(c_365, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_350])).
% 4.04/1.70  tff(c_398, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_365])).
% 4.04/1.70  tff(c_20, plain, (![A_15, B_16]: (~r1_xboole_0(k3_xboole_0(A_15, B_16), B_16) | r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.04/1.70  tff(c_404, plain, (~r1_xboole_0(k1_xboole_0, '#skF_2') | r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_398, c_20])).
% 4.04/1.70  tff(c_408, plain, (~r1_xboole_0(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_404])).
% 4.04/1.70  tff(c_30, plain, (![B_21]: (r1_tarski(k1_xboole_0, k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.70  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.70  tff(c_259, plain, (![A_57, C_58, B_59]: (r1_xboole_0(A_57, C_58) | ~r1_xboole_0(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.04/1.70  tff(c_272, plain, (![A_60]: (r1_xboole_0(A_60, '#skF_2') | ~r1_tarski(A_60, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_259])).
% 4.04/1.70  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_xboole_0(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.04/1.70  tff(c_559, plain, (![A_81, A_82]: (r1_xboole_0(A_81, '#skF_2') | ~r1_tarski(A_81, A_82) | ~r1_tarski(A_82, '#skF_3'))), inference(resolution, [status(thm)], [c_272, c_12])).
% 4.04/1.70  tff(c_571, plain, (![B_21]: (r1_xboole_0(k1_xboole_0, '#skF_2') | ~r1_tarski(k1_tarski(B_21), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_559])).
% 4.04/1.70  tff(c_582, plain, (![B_83]: (~r1_tarski(k1_tarski(B_83), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_408, c_571])).
% 4.04/1.70  tff(c_587, plain, (![A_48]: (~r2_hidden(A_48, '#skF_3'))), inference(resolution, [status(thm)], [c_220, c_582])).
% 4.04/1.70  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.70  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_587, c_38])).
% 4.04/1.70  tff(c_590, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_404])).
% 4.04/1.70  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.04/1.70  tff(c_612, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_590, c_8])).
% 4.04/1.70  tff(c_102, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.04/1.70  tff(c_105, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_102])).
% 4.04/1.70  tff(c_624, plain, (![A_84, C_85, B_86]: (~r1_xboole_0(A_84, C_85) | ~r1_xboole_0(A_84, B_86) | r1_xboole_0(A_84, k2_xboole_0(B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.04/1.70  tff(c_2095, plain, (![B_186, C_187, A_188]: (r1_xboole_0(k2_xboole_0(B_186, C_187), A_188) | ~r1_xboole_0(A_188, C_187) | ~r1_xboole_0(A_188, B_186))), inference(resolution, [status(thm)], [c_624, c_8])).
% 4.04/1.70  tff(c_34, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.70  tff(c_2115, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_2095, c_34])).
% 4.04/1.70  tff(c_2137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_612, c_105, c_2115])).
% 4.04/1.70  tff(c_2138, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_365])).
% 4.04/1.70  tff(c_2139, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_365])).
% 4.04/1.70  tff(c_2140, plain, (k1_tarski('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_2139])).
% 4.04/1.70  tff(c_271, plain, (![A_57]: (r1_xboole_0(A_57, '#skF_2') | ~r1_tarski(A_57, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_259])).
% 4.04/1.70  tff(c_2146, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_2') | r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2138, c_20])).
% 4.04/1.70  tff(c_2158, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2146])).
% 4.04/1.70  tff(c_2168, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_271, c_2158])).
% 4.04/1.70  tff(c_2173, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_220, c_2168])).
% 4.04/1.70  tff(c_2177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_2173])).
% 4.04/1.70  tff(c_2178, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2146])).
% 4.04/1.70  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.04/1.70  tff(c_2188, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2178, c_4])).
% 4.04/1.70  tff(c_2244, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2188, c_2138])).
% 4.04/1.70  tff(c_2246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2140, c_2244])).
% 4.04/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.70  
% 4.04/1.70  Inference rules
% 4.04/1.70  ----------------------
% 4.04/1.70  #Ref     : 0
% 4.04/1.70  #Sup     : 585
% 4.04/1.70  #Fact    : 0
% 4.04/1.70  #Define  : 0
% 4.04/1.70  #Split   : 7
% 4.04/1.70  #Chain   : 0
% 4.04/1.70  #Close   : 0
% 4.04/1.70  
% 4.04/1.70  Ordering : KBO
% 4.04/1.70  
% 4.04/1.70  Simplification rules
% 4.04/1.70  ----------------------
% 4.04/1.70  #Subsume      : 118
% 4.04/1.70  #Demod        : 114
% 4.04/1.70  #Tautology    : 179
% 4.04/1.70  #SimpNegUnit  : 3
% 4.04/1.70  #BackRed      : 5
% 4.04/1.70  
% 4.04/1.70  #Partial instantiations: 0
% 4.04/1.70  #Strategies tried      : 1
% 4.04/1.70  
% 4.04/1.70  Timing (in seconds)
% 4.04/1.70  ----------------------
% 4.04/1.71  Preprocessing        : 0.30
% 4.04/1.71  Parsing              : 0.16
% 4.04/1.71  CNF conversion       : 0.02
% 4.04/1.71  Main loop            : 0.64
% 4.04/1.71  Inferencing          : 0.22
% 4.04/1.71  Reduction            : 0.20
% 4.04/1.71  Demodulation         : 0.13
% 4.04/1.71  BG Simplification    : 0.02
% 4.04/1.71  Subsumption          : 0.14
% 4.04/1.71  Abstraction          : 0.03
% 4.04/1.71  MUC search           : 0.00
% 4.04/1.71  Cooper               : 0.00
% 4.04/1.71  Total                : 0.97
% 4.04/1.71  Index Insertion      : 0.00
% 4.04/1.71  Index Deletion       : 0.00
% 4.04/1.71  Index Matching       : 0.00
% 4.04/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
