%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
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

tff(f_84,axiom,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

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

tff(c_255,plain,(
    ! [B_57,A_58] :
      ( k1_tarski(B_57) = A_58
      | k1_xboole_0 = A_58
      | ~ r1_tarski(A_58,k1_tarski(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_265,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_5')
    | k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_255])).

tff(c_290,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_72,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [B_28,A_27] :
      ( r1_xboole_0(B_28,A_27)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_6])).

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

tff(c_306,plain,(
    ! [A_61,C_62,B_63] :
      ( ~ r1_xboole_0(A_61,C_62)
      | ~ r1_xboole_0(A_61,B_63)
      | r1_xboole_0(A_61,k2_xboole_0(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_527,plain,(
    ! [B_101,C_102,A_103] :
      ( r1_xboole_0(k2_xboole_0(B_101,C_102),A_103)
      | ~ r1_xboole_0(A_103,C_102)
      | ~ r1_xboole_0(A_103,B_101) ) ),
    inference(resolution,[status(thm)],[c_306,c_6])).

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
    inference(resolution,[status(thm)],[c_82,c_553])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_556])).

tff(c_564,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_565,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_566,plain,(
    k1_tarski('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_565])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),B_16)
      | r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( ~ r1_xboole_0(k3_xboole_0(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_577,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3')
    | r1_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_20])).

tff(c_581,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_593,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_581])).

tff(c_211,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,B_52)
      | ~ r2_hidden(C_53,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_229,plain,(
    ! [C_53] :
      ( ~ r2_hidden(C_53,'#skF_3')
      | ~ r2_hidden(C_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_211])).

tff(c_596,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_593,c_229])).

tff(c_600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_596])).

tff(c_601,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_611,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_601,c_2])).

tff(c_658,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_564])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.34  
% 2.67/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.67/1.34  
% 2.67/1.34  %Foreground sorts:
% 2.67/1.34  
% 2.67/1.34  
% 2.67/1.34  %Background operators:
% 2.67/1.34  
% 2.67/1.34  
% 2.67/1.34  %Foreground operators:
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.34  
% 2.67/1.36  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.67/1.36  tff(f_84, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.67/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.67/1.36  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.67/1.36  tff(f_67, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.67/1.36  tff(f_78, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.67/1.36  tff(f_73, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.67/1.36  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.67/1.36  tff(c_36, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_255, plain, (![B_57, A_58]: (k1_tarski(B_57)=A_58 | k1_xboole_0=A_58 | ~r1_tarski(A_58, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.67/1.36  tff(c_265, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_5') | k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_255])).
% 2.67/1.36  tff(c_290, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_265])).
% 2.67/1.36  tff(c_72, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.36  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.36  tff(c_82, plain, (![B_28, A_27]: (r1_xboole_0(B_28, A_27) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_6])).
% 2.67/1.36  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_39, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.36  tff(c_42, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.67/1.36  tff(c_306, plain, (![A_61, C_62, B_63]: (~r1_xboole_0(A_61, C_62) | ~r1_xboole_0(A_61, B_63) | r1_xboole_0(A_61, k2_xboole_0(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.67/1.36  tff(c_527, plain, (![B_101, C_102, A_103]: (r1_xboole_0(k2_xboole_0(B_101, C_102), A_103) | ~r1_xboole_0(A_103, C_102) | ~r1_xboole_0(A_103, B_101))), inference(resolution, [status(thm)], [c_306, c_6])).
% 2.67/1.36  tff(c_30, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_545, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_527, c_30])).
% 2.67/1.36  tff(c_553, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_545])).
% 2.67/1.36  tff(c_556, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_553])).
% 2.67/1.36  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_290, c_556])).
% 2.67/1.36  tff(c_564, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_265])).
% 2.67/1.36  tff(c_565, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_265])).
% 2.67/1.36  tff(c_566, plain, (k1_tarski('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_564, c_565])).
% 2.67/1.36  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), B_16) | r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.36  tff(c_20, plain, (![A_13, B_14]: (~r1_xboole_0(k3_xboole_0(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.36  tff(c_577, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3') | r1_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_564, c_20])).
% 2.67/1.36  tff(c_581, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_577])).
% 2.67/1.36  tff(c_593, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_581])).
% 2.67/1.36  tff(c_211, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, B_52) | ~r2_hidden(C_53, A_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.36  tff(c_229, plain, (![C_53]: (~r2_hidden(C_53, '#skF_3') | ~r2_hidden(C_53, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_211])).
% 2.67/1.36  tff(c_596, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_593, c_229])).
% 2.67/1.36  tff(c_600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_596])).
% 2.67/1.36  tff(c_601, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_577])).
% 2.67/1.36  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.36  tff(c_611, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_601, c_2])).
% 2.67/1.36  tff(c_658, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_611, c_564])).
% 2.67/1.36  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_658])).
% 2.67/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  Inference rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Ref     : 0
% 2.67/1.36  #Sup     : 151
% 2.67/1.36  #Fact    : 0
% 2.67/1.36  #Define  : 0
% 2.67/1.36  #Split   : 5
% 2.67/1.36  #Chain   : 0
% 2.67/1.36  #Close   : 0
% 2.67/1.36  
% 2.67/1.36  Ordering : KBO
% 2.67/1.36  
% 2.67/1.36  Simplification rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Subsume      : 25
% 2.67/1.36  #Demod        : 22
% 2.67/1.36  #Tautology    : 37
% 2.67/1.36  #SimpNegUnit  : 1
% 2.67/1.36  #BackRed      : 4
% 2.67/1.36  
% 2.67/1.36  #Partial instantiations: 0
% 2.67/1.36  #Strategies tried      : 1
% 2.67/1.36  
% 2.67/1.36  Timing (in seconds)
% 2.67/1.36  ----------------------
% 2.67/1.36  Preprocessing        : 0.29
% 2.67/1.36  Parsing              : 0.16
% 2.67/1.36  CNF conversion       : 0.02
% 2.67/1.36  Main loop            : 0.36
% 2.67/1.36  Inferencing          : 0.14
% 2.67/1.36  Reduction            : 0.09
% 2.67/1.36  Demodulation         : 0.06
% 2.67/1.36  BG Simplification    : 0.02
% 2.67/1.36  Subsumption          : 0.08
% 2.67/1.36  Abstraction          : 0.01
% 2.67/1.36  MUC search           : 0.00
% 2.67/1.36  Cooper               : 0.00
% 2.67/1.36  Total                : 0.68
% 2.67/1.36  Index Insertion      : 0.00
% 2.67/1.36  Index Deletion       : 0.00
% 2.67/1.36  Index Matching       : 0.00
% 2.67/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
