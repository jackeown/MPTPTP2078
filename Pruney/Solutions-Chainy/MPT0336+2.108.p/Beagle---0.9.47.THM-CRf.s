%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:15 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   58 (  99 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 180 expanded)
%              Number of equality atoms :   17 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_128,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [B_33,A_32] :
      ( r1_xboole_0(B_33,A_32)
      | k4_xboole_0(A_32,B_33) != A_32 ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_644,plain,(
    ! [A_102,C_103,B_104] :
      ( ~ r1_xboole_0(A_102,C_103)
      | ~ r1_xboole_0(A_102,B_104)
      | r1_xboole_0(A_102,k2_xboole_0(B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1472,plain,(
    ! [B_206,C_207,A_208] :
      ( r1_xboole_0(k2_xboole_0(B_206,C_207),A_208)
      | ~ r1_xboole_0(A_208,C_207)
      | ~ r1_xboole_0(A_208,B_206) ) ),
    inference(resolution,[status(thm)],[c_644,c_2])).

tff(c_32,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1490,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1472,c_32])).

tff(c_1498,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1490])).

tff(c_1509,plain,(
    k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_138,c_1498])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_56])).

tff(c_38,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,k1_tarski(B_21)) = A_20
      | r2_hidden(B_21,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_140,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | k4_xboole_0(A_35,B_34) != A_35 ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_597,plain,(
    ! [B_97,A_98] :
      ( k4_xboole_0(B_97,A_98) = B_97
      | k4_xboole_0(A_98,B_97) != A_98 ) ),
    inference(resolution,[status(thm)],[c_140,c_24])).

tff(c_1015,plain,(
    ! [B_160,A_161] :
      ( k4_xboole_0(k1_tarski(B_160),A_161) = k1_tarski(B_160)
      | r2_hidden(B_160,A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_597])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1911,plain,(
    ! [A_254,A_255,B_256] :
      ( r1_xboole_0(A_254,A_255)
      | ~ r1_tarski(A_254,k1_tarski(B_256))
      | r2_hidden(B_256,A_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_10])).

tff(c_1915,plain,(
    ! [A_257] :
      ( r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),A_257)
      | r2_hidden('#skF_5',A_257) ) ),
    inference(resolution,[status(thm)],[c_38,c_1911])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( ~ r1_xboole_0(k3_xboole_0(A_14,B_15),B_15)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1938,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1915,c_20])).

tff(c_1941,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1938])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_497,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,B_89)
      | ~ r2_hidden(C_90,A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1761,plain,(
    ! [C_233,A_234,B_235] :
      ( ~ r2_hidden(C_233,A_234)
      | ~ r2_hidden(C_233,B_235)
      | k4_xboole_0(A_234,B_235) != A_234 ) ),
    inference(resolution,[status(thm)],[c_138,c_497])).

tff(c_1785,plain,(
    ! [B_235] :
      ( ~ r2_hidden('#skF_5',B_235)
      | k4_xboole_0('#skF_4',B_235) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_36,c_1761])).

tff(c_1944,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1941,c_1785])).

tff(c_1963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1944])).

tff(c_1964,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1938])).

tff(c_1970,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1964,c_24])).

tff(c_1977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1509,c_1970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.64  
% 3.71/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.71/1.64  
% 3.71/1.64  %Foreground sorts:
% 3.71/1.64  
% 3.71/1.64  
% 3.71/1.64  %Background operators:
% 3.71/1.64  
% 3.71/1.64  
% 3.71/1.64  %Foreground operators:
% 3.71/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.71/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.71/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.71/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.71/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.71/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.71/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.71/1.64  
% 3.71/1.66  tff(f_81, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.71/1.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.71/1.66  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.71/1.66  tff(f_69, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.71/1.66  tff(f_86, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.71/1.66  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.71/1.66  tff(f_75, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.71/1.66  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.71/1.66  tff(c_128, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k4_xboole_0(A_32, B_33)!=A_32)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.71/1.66  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.71/1.66  tff(c_138, plain, (![B_33, A_32]: (r1_xboole_0(B_33, A_32) | k4_xboole_0(A_32, B_33)!=A_32)), inference(resolution, [status(thm)], [c_128, c_2])).
% 3.71/1.66  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.71/1.66  tff(c_40, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.71/1.66  tff(c_46, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_40])).
% 3.71/1.66  tff(c_644, plain, (![A_102, C_103, B_104]: (~r1_xboole_0(A_102, C_103) | ~r1_xboole_0(A_102, B_104) | r1_xboole_0(A_102, k2_xboole_0(B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.71/1.66  tff(c_1472, plain, (![B_206, C_207, A_208]: (r1_xboole_0(k2_xboole_0(B_206, C_207), A_208) | ~r1_xboole_0(A_208, C_207) | ~r1_xboole_0(A_208, B_206))), inference(resolution, [status(thm)], [c_644, c_2])).
% 3.71/1.66  tff(c_32, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.71/1.66  tff(c_1490, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1472, c_32])).
% 3.71/1.66  tff(c_1498, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1490])).
% 3.71/1.66  tff(c_1509, plain, (k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_138, c_1498])).
% 3.71/1.66  tff(c_56, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.71/1.66  tff(c_72, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_56])).
% 3.71/1.66  tff(c_38, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.71/1.66  tff(c_30, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k1_tarski(B_21))=A_20 | r2_hidden(B_21, A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.71/1.66  tff(c_140, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | k4_xboole_0(A_35, B_34)!=A_35)), inference(resolution, [status(thm)], [c_128, c_2])).
% 3.71/1.66  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.71/1.66  tff(c_597, plain, (![B_97, A_98]: (k4_xboole_0(B_97, A_98)=B_97 | k4_xboole_0(A_98, B_97)!=A_98)), inference(resolution, [status(thm)], [c_140, c_24])).
% 3.71/1.66  tff(c_1015, plain, (![B_160, A_161]: (k4_xboole_0(k1_tarski(B_160), A_161)=k1_tarski(B_160) | r2_hidden(B_160, A_161))), inference(superposition, [status(thm), theory('equality')], [c_30, c_597])).
% 3.71/1.66  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.71/1.66  tff(c_1911, plain, (![A_254, A_255, B_256]: (r1_xboole_0(A_254, A_255) | ~r1_tarski(A_254, k1_tarski(B_256)) | r2_hidden(B_256, A_255))), inference(superposition, [status(thm), theory('equality')], [c_1015, c_10])).
% 3.71/1.66  tff(c_1915, plain, (![A_257]: (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), A_257) | r2_hidden('#skF_5', A_257))), inference(resolution, [status(thm)], [c_38, c_1911])).
% 3.71/1.66  tff(c_20, plain, (![A_14, B_15]: (~r1_xboole_0(k3_xboole_0(A_14, B_15), B_15) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.71/1.66  tff(c_1938, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1915, c_20])).
% 3.71/1.66  tff(c_1941, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1938])).
% 3.71/1.66  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.71/1.66  tff(c_497, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, B_89) | ~r2_hidden(C_90, A_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.71/1.66  tff(c_1761, plain, (![C_233, A_234, B_235]: (~r2_hidden(C_233, A_234) | ~r2_hidden(C_233, B_235) | k4_xboole_0(A_234, B_235)!=A_234)), inference(resolution, [status(thm)], [c_138, c_497])).
% 3.71/1.66  tff(c_1785, plain, (![B_235]: (~r2_hidden('#skF_5', B_235) | k4_xboole_0('#skF_4', B_235)!='#skF_4')), inference(resolution, [status(thm)], [c_36, c_1761])).
% 3.71/1.66  tff(c_1944, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_1941, c_1785])).
% 3.71/1.66  tff(c_1963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1944])).
% 3.71/1.66  tff(c_1964, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1938])).
% 3.71/1.66  tff(c_1970, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_1964, c_24])).
% 3.71/1.66  tff(c_1977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1509, c_1970])).
% 3.71/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.66  
% 3.71/1.66  Inference rules
% 3.71/1.66  ----------------------
% 3.71/1.66  #Ref     : 0
% 3.71/1.66  #Sup     : 479
% 3.71/1.66  #Fact    : 0
% 3.71/1.66  #Define  : 0
% 3.71/1.66  #Split   : 1
% 3.71/1.66  #Chain   : 0
% 3.71/1.66  #Close   : 0
% 3.71/1.66  
% 3.71/1.66  Ordering : KBO
% 3.71/1.66  
% 3.71/1.66  Simplification rules
% 3.71/1.66  ----------------------
% 3.71/1.66  #Subsume      : 79
% 3.71/1.66  #Demod        : 68
% 3.71/1.66  #Tautology    : 123
% 3.71/1.66  #SimpNegUnit  : 3
% 3.71/1.66  #BackRed      : 0
% 3.71/1.66  
% 3.71/1.66  #Partial instantiations: 0
% 3.71/1.66  #Strategies tried      : 1
% 3.71/1.66  
% 3.71/1.66  Timing (in seconds)
% 3.71/1.66  ----------------------
% 3.71/1.66  Preprocessing        : 0.28
% 3.71/1.66  Parsing              : 0.16
% 3.71/1.66  CNF conversion       : 0.02
% 3.71/1.66  Main loop            : 0.61
% 3.71/1.66  Inferencing          : 0.23
% 3.71/1.66  Reduction            : 0.17
% 3.71/1.66  Demodulation         : 0.12
% 3.71/1.66  BG Simplification    : 0.02
% 3.71/1.66  Subsumption          : 0.13
% 3.71/1.66  Abstraction          : 0.03
% 3.71/1.66  MUC search           : 0.00
% 3.71/1.66  Cooper               : 0.00
% 3.71/1.66  Total                : 0.93
% 3.71/1.66  Index Insertion      : 0.00
% 3.71/1.66  Index Deletion       : 0.00
% 3.71/1.66  Index Matching       : 0.00
% 3.71/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
