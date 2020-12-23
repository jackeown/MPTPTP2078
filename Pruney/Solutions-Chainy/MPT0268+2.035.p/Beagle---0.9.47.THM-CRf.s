%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:38 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 (  99 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_65,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_352,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(k1_tarski(A_76),B_77) = k1_xboole_0
      | r2_hidden(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_212])).

tff(c_358,plain,(
    ! [B_77,A_76] :
      ( k4_xboole_0(B_77,k1_tarski(A_76)) = k5_xboole_0(B_77,k1_xboole_0)
      | r2_hidden(A_76,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_227])).

tff(c_553,plain,(
    ! [B_90,A_91] :
      ( k4_xboole_0(B_90,k1_tarski(A_91)) = B_90
      | r2_hidden(A_91,B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_358])).

tff(c_30,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_181,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_572,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_181])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_572])).

tff(c_600,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_601,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_638,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_34])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [B_16,A_15] : r1_xboole_0(B_16,k4_xboole_0(A_15,B_16)) ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_104,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,B_45)
      | ~ r1_xboole_0(k1_tarski(A_44),B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_113,plain,(
    ! [A_44,A_15] : ~ r2_hidden(A_44,k4_xboole_0(A_15,k1_tarski(A_44))) ),
    inference(resolution,[status(thm)],[c_59,c_104])).

tff(c_645,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_113])).

tff(c_656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_645])).

tff(c_657,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_658,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_795,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_36])).

tff(c_706,plain,(
    ! [A_99,B_100] :
      ( ~ r2_hidden(A_99,B_100)
      | ~ r1_xboole_0(k1_tarski(A_99),B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_715,plain,(
    ! [A_99,A_15] : ~ r2_hidden(A_99,k4_xboole_0(A_15,k1_tarski(A_99))) ),
    inference(resolution,[status(thm)],[c_59,c_706])).

tff(c_802,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_715])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.36  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.48/1.36  
% 2.48/1.36  %Foreground sorts:
% 2.48/1.36  
% 2.48/1.36  
% 2.48/1.36  %Background operators:
% 2.48/1.36  
% 2.48/1.36  
% 2.48/1.36  %Foreground operators:
% 2.48/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.36  
% 2.48/1.38  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.48/1.38  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.48/1.38  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.48/1.38  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.48/1.38  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.48/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.48/1.38  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.48/1.38  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.48/1.38  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.48/1.38  tff(f_72, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.48/1.38  tff(c_32, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.38  tff(c_65, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.48/1.38  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.38  tff(c_28, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.48/1.38  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.38  tff(c_133, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.48/1.38  tff(c_145, plain, (![A_55, B_56]: (~r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_133])).
% 2.48/1.38  tff(c_352, plain, (![A_76, B_77]: (k3_xboole_0(k1_tarski(A_76), B_77)=k1_xboole_0 | r2_hidden(A_76, B_77))), inference(resolution, [status(thm)], [c_28, c_145])).
% 2.48/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.38  tff(c_212, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.38  tff(c_227, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_212])).
% 2.48/1.38  tff(c_358, plain, (![B_77, A_76]: (k4_xboole_0(B_77, k1_tarski(A_76))=k5_xboole_0(B_77, k1_xboole_0) | r2_hidden(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_352, c_227])).
% 2.48/1.38  tff(c_553, plain, (![B_90, A_91]: (k4_xboole_0(B_90, k1_tarski(A_91))=B_90 | r2_hidden(A_91, B_90))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_358])).
% 2.48/1.38  tff(c_30, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.38  tff(c_181, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.48/1.38  tff(c_572, plain, (r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_553, c_181])).
% 2.48/1.38  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_572])).
% 2.48/1.38  tff(c_600, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 2.48/1.38  tff(c_601, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.48/1.38  tff(c_34, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.38  tff(c_638, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_601, c_34])).
% 2.48/1.38  tff(c_16, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.38  tff(c_56, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.38  tff(c_59, plain, (![B_16, A_15]: (r1_xboole_0(B_16, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_16, c_56])).
% 2.48/1.38  tff(c_104, plain, (![A_44, B_45]: (~r2_hidden(A_44, B_45) | ~r1_xboole_0(k1_tarski(A_44), B_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.38  tff(c_113, plain, (![A_44, A_15]: (~r2_hidden(A_44, k4_xboole_0(A_15, k1_tarski(A_44))))), inference(resolution, [status(thm)], [c_59, c_104])).
% 2.48/1.38  tff(c_645, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_638, c_113])).
% 2.48/1.38  tff(c_656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_600, c_645])).
% 2.48/1.38  tff(c_657, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 2.48/1.38  tff(c_658, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.48/1.38  tff(c_36, plain, (~r2_hidden('#skF_4', '#skF_3') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.38  tff(c_795, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_36])).
% 2.48/1.38  tff(c_706, plain, (![A_99, B_100]: (~r2_hidden(A_99, B_100) | ~r1_xboole_0(k1_tarski(A_99), B_100))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.38  tff(c_715, plain, (![A_99, A_15]: (~r2_hidden(A_99, k4_xboole_0(A_15, k1_tarski(A_99))))), inference(resolution, [status(thm)], [c_59, c_706])).
% 2.48/1.38  tff(c_802, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_795, c_715])).
% 2.48/1.38  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_657, c_802])).
% 2.48/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.38  
% 2.48/1.38  Inference rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Ref     : 0
% 2.48/1.38  #Sup     : 186
% 2.48/1.38  #Fact    : 0
% 2.48/1.38  #Define  : 0
% 2.48/1.38  #Split   : 2
% 2.48/1.38  #Chain   : 0
% 2.48/1.38  #Close   : 0
% 2.48/1.38  
% 2.48/1.38  Ordering : KBO
% 2.48/1.38  
% 2.48/1.38  Simplification rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Subsume      : 31
% 2.48/1.38  #Demod        : 49
% 2.48/1.38  #Tautology    : 96
% 2.48/1.38  #SimpNegUnit  : 10
% 2.48/1.38  #BackRed      : 0
% 2.48/1.38  
% 2.48/1.38  #Partial instantiations: 0
% 2.48/1.38  #Strategies tried      : 1
% 2.48/1.38  
% 2.48/1.38  Timing (in seconds)
% 2.48/1.38  ----------------------
% 2.48/1.38  Preprocessing        : 0.29
% 2.48/1.38  Parsing              : 0.15
% 2.48/1.38  CNF conversion       : 0.02
% 2.48/1.38  Main loop            : 0.28
% 2.48/1.38  Inferencing          : 0.11
% 2.48/1.38  Reduction            : 0.09
% 2.48/1.38  Demodulation         : 0.07
% 2.48/1.38  BG Simplification    : 0.01
% 2.48/1.38  Subsumption          : 0.04
% 2.48/1.38  Abstraction          : 0.02
% 2.48/1.38  MUC search           : 0.00
% 2.48/1.38  Cooper               : 0.00
% 2.48/1.38  Total                : 0.60
% 2.48/1.38  Index Insertion      : 0.00
% 2.48/1.38  Index Deletion       : 0.00
% 2.48/1.38  Index Matching       : 0.00
% 2.48/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
