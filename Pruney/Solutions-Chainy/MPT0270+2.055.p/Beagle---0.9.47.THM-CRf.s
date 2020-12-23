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
% DateTime   : Thu Dec  3 09:52:59 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   62 (  77 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  86 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_63,B_64] :
      ( ~ r1_xboole_0(A_63,B_64)
      | k3_xboole_0(A_63,B_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_110])).

tff(c_325,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(k1_tarski(A_88),B_89) = k1_xboole_0
      | r2_hidden(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_32,c_122])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_341,plain,(
    ! [A_88,B_89] :
      ( k5_xboole_0(k1_tarski(A_88),k1_xboole_0) = k4_xboole_0(k1_tarski(A_88),B_89)
      | r2_hidden(A_88,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_10])).

tff(c_618,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(k1_tarski(A_119),B_120) = k1_tarski(A_119)
      | r2_hidden(A_119,B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_341])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_199,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_645,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_199])).

tff(c_674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_645])).

tff(c_675,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_676,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_734,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_38])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_744,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_14])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(A_43,B_44)
      | ~ r1_xboole_0(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_753,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_744,c_30])).

tff(c_758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_753])).

tff(c_759,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_760,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_824,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_40])).

tff(c_831,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_14])).

tff(c_847,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_831,c_30])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.74/1.41  
% 2.74/1.41  %Foreground sorts:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Background operators:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Foreground operators:
% 2.74/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.74/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.41  
% 2.74/1.42  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.74/1.42  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.74/1.42  tff(f_79, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.74/1.42  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.74/1.42  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.74/1.42  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.74/1.42  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.74/1.42  tff(f_74, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.74/1.42  tff(c_36, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.42  tff(c_94, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 2.74/1.42  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.42  tff(c_32, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.42  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.42  tff(c_110, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.42  tff(c_122, plain, (![A_63, B_64]: (~r1_xboole_0(A_63, B_64) | k3_xboole_0(A_63, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_110])).
% 2.74/1.42  tff(c_325, plain, (![A_88, B_89]: (k3_xboole_0(k1_tarski(A_88), B_89)=k1_xboole_0 | r2_hidden(A_88, B_89))), inference(resolution, [status(thm)], [c_32, c_122])).
% 2.74/1.42  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.74/1.42  tff(c_341, plain, (![A_88, B_89]: (k5_xboole_0(k1_tarski(A_88), k1_xboole_0)=k4_xboole_0(k1_tarski(A_88), B_89) | r2_hidden(A_88, B_89))), inference(superposition, [status(thm), theory('equality')], [c_325, c_10])).
% 2.74/1.42  tff(c_618, plain, (![A_119, B_120]: (k4_xboole_0(k1_tarski(A_119), B_120)=k1_tarski(A_119) | r2_hidden(A_119, B_120))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_341])).
% 2.74/1.42  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.42  tff(c_199, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.74/1.42  tff(c_645, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_618, c_199])).
% 2.74/1.42  tff(c_674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_645])).
% 2.74/1.42  tff(c_675, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 2.74/1.42  tff(c_676, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.74/1.42  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.42  tff(c_734, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_676, c_38])).
% 2.74/1.42  tff(c_14, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.42  tff(c_744, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_734, c_14])).
% 2.74/1.42  tff(c_30, plain, (![A_43, B_44]: (~r2_hidden(A_43, B_44) | ~r1_xboole_0(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.42  tff(c_753, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_744, c_30])).
% 2.74/1.42  tff(c_758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_675, c_753])).
% 2.74/1.42  tff(c_759, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 2.74/1.42  tff(c_760, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.74/1.42  tff(c_40, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.42  tff(c_824, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_40])).
% 2.74/1.42  tff(c_831, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_824, c_14])).
% 2.74/1.42  tff(c_847, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_831, c_30])).
% 2.74/1.42  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_759, c_847])).
% 2.74/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.42  
% 2.74/1.42  Inference rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Ref     : 0
% 2.74/1.42  #Sup     : 195
% 2.74/1.42  #Fact    : 0
% 2.74/1.42  #Define  : 0
% 2.74/1.42  #Split   : 2
% 2.74/1.42  #Chain   : 0
% 2.74/1.42  #Close   : 0
% 2.74/1.42  
% 2.74/1.42  Ordering : KBO
% 2.74/1.42  
% 2.74/1.42  Simplification rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Subsume      : 36
% 2.74/1.42  #Demod        : 51
% 2.74/1.42  #Tautology    : 105
% 2.74/1.42  #SimpNegUnit  : 12
% 2.74/1.42  #BackRed      : 0
% 2.74/1.42  
% 2.74/1.42  #Partial instantiations: 0
% 2.74/1.42  #Strategies tried      : 1
% 2.74/1.42  
% 2.74/1.42  Timing (in seconds)
% 2.74/1.42  ----------------------
% 2.74/1.43  Preprocessing        : 0.32
% 2.74/1.43  Parsing              : 0.18
% 2.74/1.43  CNF conversion       : 0.02
% 2.74/1.43  Main loop            : 0.30
% 2.74/1.43  Inferencing          : 0.12
% 2.74/1.43  Reduction            : 0.10
% 2.74/1.43  Demodulation         : 0.07
% 2.74/1.43  BG Simplification    : 0.02
% 2.74/1.43  Subsumption          : 0.04
% 2.74/1.43  Abstraction          : 0.02
% 2.74/1.43  MUC search           : 0.00
% 2.74/1.43  Cooper               : 0.00
% 2.74/1.43  Total                : 0.66
% 2.74/1.43  Index Insertion      : 0.00
% 2.74/1.43  Index Deletion       : 0.00
% 2.74/1.43  Index Matching       : 0.00
% 2.74/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
