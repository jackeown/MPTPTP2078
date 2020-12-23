%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   58 (  98 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 180 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_51,axiom,(
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

tff(c_36,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_211,plain,(
    ! [B_51,A_52] :
      ( k1_tarski(B_51) = A_52
      | k1_xboole_0 = A_52
      | ~ r1_tarski(A_52,k1_tarski(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_221,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_5')
    | k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_211])).

tff(c_256,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_64,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [B_26,A_25] :
      ( r1_xboole_0(B_26,A_25)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_39,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_289,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r1_xboole_0(A_57,C_58)
      | ~ r1_xboole_0(A_57,B_59)
      | r1_xboole_0(A_57,k2_xboole_0(B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_527,plain,(
    ! [B_103,C_104,A_105] :
      ( r1_xboole_0(k2_xboole_0(B_103,C_104),A_105)
      | ~ r1_xboole_0(A_105,C_104)
      | ~ r1_xboole_0(A_105,B_103) ) ),
    inference(resolution,[status(thm)],[c_289,c_6])).

tff(c_30,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_545,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_527,c_30])).

tff(c_553,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_545])).

tff(c_556,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_553])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_556])).

tff(c_564,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_565,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_566,plain,(
    k1_tarski('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_565])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),B_18)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( ~ r1_xboole_0(k3_xboole_0(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_574,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3')
    | r1_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_20])).

tff(c_578,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_589,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_578])).

tff(c_226,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,B_54)
      | ~ r2_hidden(C_55,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_244,plain,(
    ! [C_55] :
      ( ~ r2_hidden(C_55,'#skF_3')
      | ~ r2_hidden(C_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_226])).

tff(c_593,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_589,c_244])).

tff(c_597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_593])).

tff(c_598,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_608,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_598,c_2])).

tff(c_655,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_564])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/2.02  
% 3.32/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/2.03  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/2.03  
% 3.32/2.03  %Foreground sorts:
% 3.32/2.03  
% 3.32/2.03  
% 3.32/2.03  %Background operators:
% 3.32/2.03  
% 3.32/2.03  
% 3.32/2.03  %Foreground operators:
% 3.32/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/2.03  tff('#skF_5', type, '#skF_5': $i).
% 3.32/2.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/2.03  tff('#skF_2', type, '#skF_2': $i).
% 3.32/2.03  tff('#skF_3', type, '#skF_3': $i).
% 3.32/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/2.03  tff('#skF_4', type, '#skF_4': $i).
% 3.32/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/2.03  
% 3.32/2.05  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.32/2.05  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.32/2.05  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.32/2.05  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.32/2.05  tff(f_67, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.32/2.05  tff(f_84, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 3.32/2.05  tff(f_73, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.32/2.05  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.32/2.05  tff(c_36, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/2.05  tff(c_211, plain, (![B_51, A_52]: (k1_tarski(B_51)=A_52 | k1_xboole_0=A_52 | ~r1_tarski(A_52, k1_tarski(B_51)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.32/2.05  tff(c_221, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_5') | k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_211])).
% 3.32/2.05  tff(c_256, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_221])).
% 3.32/2.05  tff(c_64, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/2.05  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/2.05  tff(c_74, plain, (![B_26, A_25]: (r1_xboole_0(B_26, A_25) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_6])).
% 3.32/2.05  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/2.05  tff(c_39, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/2.05  tff(c_42, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_39])).
% 3.32/2.05  tff(c_289, plain, (![A_57, C_58, B_59]: (~r1_xboole_0(A_57, C_58) | ~r1_xboole_0(A_57, B_59) | r1_xboole_0(A_57, k2_xboole_0(B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/2.05  tff(c_527, plain, (![B_103, C_104, A_105]: (r1_xboole_0(k2_xboole_0(B_103, C_104), A_105) | ~r1_xboole_0(A_105, C_104) | ~r1_xboole_0(A_105, B_103))), inference(resolution, [status(thm)], [c_289, c_6])).
% 3.32/2.05  tff(c_30, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/2.05  tff(c_545, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_527, c_30])).
% 3.32/2.05  tff(c_553, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_545])).
% 3.32/2.05  tff(c_556, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_553])).
% 3.32/2.05  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_556])).
% 3.32/2.05  tff(c_564, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_221])).
% 3.32/2.05  tff(c_565, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_221])).
% 3.32/2.05  tff(c_566, plain, (k1_tarski('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_564, c_565])).
% 3.32/2.05  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/2.05  tff(c_28, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), B_18) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.32/2.05  tff(c_20, plain, (![A_13, B_14]: (~r1_xboole_0(k3_xboole_0(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.32/2.05  tff(c_574, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3') | r1_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_564, c_20])).
% 3.32/2.05  tff(c_578, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_574])).
% 3.32/2.05  tff(c_589, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_578])).
% 3.32/2.05  tff(c_226, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, B_54) | ~r2_hidden(C_55, A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/2.05  tff(c_244, plain, (![C_55]: (~r2_hidden(C_55, '#skF_3') | ~r2_hidden(C_55, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_226])).
% 3.32/2.05  tff(c_593, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_589, c_244])).
% 3.32/2.05  tff(c_597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_593])).
% 3.32/2.05  tff(c_598, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_574])).
% 3.32/2.05  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/2.05  tff(c_608, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_598, c_2])).
% 3.32/2.05  tff(c_655, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_608, c_564])).
% 3.32/2.05  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_655])).
% 3.32/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/2.05  
% 3.32/2.05  Inference rules
% 3.32/2.05  ----------------------
% 3.32/2.05  #Ref     : 0
% 3.32/2.05  #Sup     : 150
% 3.32/2.05  #Fact    : 0
% 3.32/2.05  #Define  : 0
% 3.32/2.05  #Split   : 4
% 3.32/2.05  #Chain   : 0
% 3.32/2.05  #Close   : 0
% 3.32/2.05  
% 3.32/2.05  Ordering : KBO
% 3.32/2.05  
% 3.32/2.05  Simplification rules
% 3.32/2.05  ----------------------
% 3.32/2.05  #Subsume      : 29
% 3.32/2.05  #Demod        : 22
% 3.32/2.05  #Tautology    : 36
% 3.32/2.05  #SimpNegUnit  : 1
% 3.32/2.05  #BackRed      : 4
% 3.32/2.05  
% 3.32/2.05  #Partial instantiations: 0
% 3.32/2.05  #Strategies tried      : 1
% 3.32/2.05  
% 3.32/2.05  Timing (in seconds)
% 3.32/2.05  ----------------------
% 3.32/2.05  Preprocessing        : 0.44
% 3.32/2.05  Parsing              : 0.24
% 3.32/2.05  CNF conversion       : 0.03
% 3.32/2.05  Main loop            : 0.71
% 3.32/2.05  Inferencing          : 0.26
% 3.32/2.05  Reduction            : 0.16
% 3.32/2.05  Demodulation         : 0.11
% 3.32/2.05  BG Simplification    : 0.03
% 3.32/2.05  Subsumption          : 0.17
% 3.32/2.05  Abstraction          : 0.02
% 3.32/2.05  MUC search           : 0.00
% 3.32/2.05  Cooper               : 0.00
% 3.32/2.06  Total                : 1.20
% 3.32/2.06  Index Insertion      : 0.00
% 3.32/2.06  Index Deletion       : 0.00
% 3.32/2.06  Index Matching       : 0.00
% 3.32/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
