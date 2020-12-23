%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:09 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 157 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 240 expanded)
%              Number of equality atoms :   39 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_85,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_53,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_30,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [B_26,A_25] : r1_xboole_0(B_26,k4_xboole_0(A_25,B_26)) ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_121,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = A_48
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_138,plain,(
    ! [B_26,A_25] : k4_xboole_0(B_26,k4_xboole_0(A_25,B_26)) = B_26 ),
    inference(resolution,[status(thm)],[c_69,c_121])).

tff(c_202,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,(
    ! [B_26,A_25] : k3_xboole_0(B_26,k4_xboole_0(A_25,B_26)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_202])).

tff(c_496,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_511,plain,(
    ! [B_26,A_25] : k4_xboole_0(B_26,k4_xboole_0(A_25,B_26)) = k5_xboole_0(B_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_496])).

tff(c_529,plain,(
    ! [B_26] : k5_xboole_0(B_26,k1_xboole_0) = B_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_511])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_377,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,k1_tarski(B_69)) = A_68
      | r2_hidden(B_69,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_427,plain,(
    ! [A_73,B_74] :
      ( r1_xboole_0(A_73,k1_tarski(B_74))
      | r2_hidden(B_74,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_30])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_438,plain,(
    ! [B_74,A_73] :
      ( r1_xboole_0(k1_tarski(B_74),A_73)
      | r2_hidden(B_74,A_73) ) ),
    inference(resolution,[status(thm)],[c_427,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_197,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_201,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_197])).

tff(c_44,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,k1_tarski(B_36)) = A_35
      | r2_hidden(B_36,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3447,plain,(
    ! [A_181,B_182] :
      ( k3_xboole_0(A_181,B_182) = k1_xboole_0
      | k4_xboole_0(A_181,B_182) != A_181 ) ),
    inference(resolution,[status(thm)],[c_34,c_202])).

tff(c_3712,plain,(
    ! [A_185,B_186] :
      ( k3_xboole_0(A_185,k1_tarski(B_186)) = k1_xboole_0
      | r2_hidden(B_186,A_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3447])).

tff(c_3827,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_3712])).

tff(c_4577,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3827])).

tff(c_301,plain,(
    ! [A_60,B_61] :
      ( r1_xboole_0(A_60,B_61)
      | k3_xboole_0(A_60,B_61) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3510,plain,(
    ! [A_183,B_184] :
      ( k4_xboole_0(A_183,B_184) = A_183
      | k3_xboole_0(A_183,B_184) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_301,c_32])).

tff(c_42,plain,(
    ! [B_36,A_35] :
      ( ~ r2_hidden(B_36,A_35)
      | k4_xboole_0(A_35,k1_tarski(B_36)) != A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4578,plain,(
    ! [B_198,A_199] :
      ( ~ r2_hidden(B_198,A_199)
      | k3_xboole_0(A_199,k1_tarski(B_198)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3510,c_42])).

tff(c_4596,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2'))
    | k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_4578])).

tff(c_4613,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4577,c_4596])).

tff(c_553,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | r1_xboole_0(A_92,k3_xboole_0(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3872,plain,(
    ! [A_187,B_188,C_189] :
      ( k3_xboole_0(A_187,k3_xboole_0(B_188,C_189)) = k1_xboole_0
      | ~ r1_xboole_0(A_187,B_188) ) ),
    inference(resolution,[status(thm)],[c_553,c_4])).

tff(c_323,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_2])).

tff(c_4010,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3872,c_323])).

tff(c_5906,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_4613,c_4010])).

tff(c_5922,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_438,c_5906])).

tff(c_48,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_834,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,B_107)
      | ~ r2_hidden(C_108,A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_879,plain,(
    ! [C_108] :
      ( ~ r2_hidden(C_108,'#skF_3')
      | ~ r2_hidden(C_108,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_834])).

tff(c_5930,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5922,c_879])).

tff(c_5934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5930])).

tff(c_5935,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3827])).

tff(c_526,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_496])).

tff(c_5964,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5935,c_526])).

tff(c_5997,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_5964])).

tff(c_6133,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_69])).

tff(c_70,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_1400,plain,(
    ! [A_132,C_133,B_134] :
      ( ~ r1_xboole_0(A_132,C_133)
      | ~ r1_xboole_0(A_132,B_134)
      | r1_xboole_0(A_132,k2_xboole_0(B_134,C_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11462,plain,(
    ! [B_298,C_299,A_300] :
      ( r1_xboole_0(k2_xboole_0(B_298,C_299),A_300)
      | ~ r1_xboole_0(A_300,C_299)
      | ~ r1_xboole_0(A_300,B_298) ) ),
    inference(resolution,[status(thm)],[c_1400,c_8])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_11483,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_11462,c_46])).

tff(c_11493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6133,c_70,c_11483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.26/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/2.66  
% 7.26/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/2.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.26/2.66  
% 7.26/2.66  %Foreground sorts:
% 7.26/2.66  
% 7.26/2.66  
% 7.26/2.66  %Background operators:
% 7.26/2.66  
% 7.26/2.66  
% 7.26/2.66  %Foreground operators:
% 7.26/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.26/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.26/2.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.26/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.26/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.26/2.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.26/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.26/2.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.26/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.26/2.66  tff('#skF_5', type, '#skF_5': $i).
% 7.26/2.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.26/2.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.26/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.26/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.26/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.26/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.26/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.26/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.26/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.26/2.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.26/2.66  
% 7.26/2.68  tff(f_85, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.26/2.68  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.26/2.68  tff(f_89, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.26/2.68  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.26/2.68  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.26/2.68  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.26/2.68  tff(f_100, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.26/2.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.26/2.68  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.26/2.68  tff(f_83, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 7.26/2.68  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.26/2.68  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.26/2.68  tff(c_30, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.26/2.68  tff(c_64, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.26/2.68  tff(c_69, plain, (![B_26, A_25]: (r1_xboole_0(B_26, k4_xboole_0(A_25, B_26)))), inference(resolution, [status(thm)], [c_30, c_64])).
% 7.26/2.68  tff(c_121, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=A_48 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.26/2.68  tff(c_138, plain, (![B_26, A_25]: (k4_xboole_0(B_26, k4_xboole_0(A_25, B_26))=B_26)), inference(resolution, [status(thm)], [c_69, c_121])).
% 7.26/2.68  tff(c_202, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.26/2.68  tff(c_219, plain, (![B_26, A_25]: (k3_xboole_0(B_26, k4_xboole_0(A_25, B_26))=k1_xboole_0)), inference(resolution, [status(thm)], [c_69, c_202])).
% 7.26/2.68  tff(c_496, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.26/2.68  tff(c_511, plain, (![B_26, A_25]: (k4_xboole_0(B_26, k4_xboole_0(A_25, B_26))=k5_xboole_0(B_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_219, c_496])).
% 7.26/2.68  tff(c_529, plain, (![B_26]: (k5_xboole_0(B_26, k1_xboole_0)=B_26)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_511])).
% 7.26/2.68  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.26/2.68  tff(c_377, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k1_tarski(B_69))=A_68 | r2_hidden(B_69, A_68))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.26/2.68  tff(c_427, plain, (![A_73, B_74]: (r1_xboole_0(A_73, k1_tarski(B_74)) | r2_hidden(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_377, c_30])).
% 7.26/2.68  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.26/2.68  tff(c_438, plain, (![B_74, A_73]: (r1_xboole_0(k1_tarski(B_74), A_73) | r2_hidden(B_74, A_73))), inference(resolution, [status(thm)], [c_427, c_8])).
% 7.26/2.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.26/2.68  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.26/2.68  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 7.26/2.68  tff(c_197, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.26/2.68  tff(c_201, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_197])).
% 7.26/2.68  tff(c_44, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k1_tarski(B_36))=A_35 | r2_hidden(B_36, A_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.26/2.68  tff(c_34, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k4_xboole_0(A_27, B_28)!=A_27)), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.26/2.68  tff(c_3447, plain, (![A_181, B_182]: (k3_xboole_0(A_181, B_182)=k1_xboole_0 | k4_xboole_0(A_181, B_182)!=A_181)), inference(resolution, [status(thm)], [c_34, c_202])).
% 7.26/2.68  tff(c_3712, plain, (![A_185, B_186]: (k3_xboole_0(A_185, k1_tarski(B_186))=k1_xboole_0 | r2_hidden(B_186, A_185))), inference(superposition, [status(thm), theory('equality')], [c_44, c_3447])).
% 7.26/2.68  tff(c_3827, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_3712])).
% 7.26/2.68  tff(c_4577, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3827])).
% 7.26/2.68  tff(c_301, plain, (![A_60, B_61]: (r1_xboole_0(A_60, B_61) | k3_xboole_0(A_60, B_61)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.26/2.68  tff(c_32, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.26/2.68  tff(c_3510, plain, (![A_183, B_184]: (k4_xboole_0(A_183, B_184)=A_183 | k3_xboole_0(A_183, B_184)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_301, c_32])).
% 7.26/2.68  tff(c_42, plain, (![B_36, A_35]: (~r2_hidden(B_36, A_35) | k4_xboole_0(A_35, k1_tarski(B_36))!=A_35)), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.26/2.68  tff(c_4578, plain, (![B_198, A_199]: (~r2_hidden(B_198, A_199) | k3_xboole_0(A_199, k1_tarski(B_198))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3510, c_42])).
% 7.26/2.68  tff(c_4596, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2')) | k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_201, c_4578])).
% 7.26/2.68  tff(c_4613, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4577, c_4596])).
% 7.26/2.68  tff(c_553, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | r1_xboole_0(A_92, k3_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.26/2.68  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.26/2.68  tff(c_3872, plain, (![A_187, B_188, C_189]: (k3_xboole_0(A_187, k3_xboole_0(B_188, C_189))=k1_xboole_0 | ~r1_xboole_0(A_187, B_188))), inference(resolution, [status(thm)], [c_553, c_4])).
% 7.26/2.68  tff(c_323, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_201, c_2])).
% 7.26/2.68  tff(c_4010, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3872, c_323])).
% 7.26/2.68  tff(c_5906, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_4613, c_4010])).
% 7.26/2.68  tff(c_5922, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_438, c_5906])).
% 7.26/2.68  tff(c_48, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.26/2.68  tff(c_834, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, B_107) | ~r2_hidden(C_108, A_106))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.26/2.68  tff(c_879, plain, (![C_108]: (~r2_hidden(C_108, '#skF_3') | ~r2_hidden(C_108, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_834])).
% 7.26/2.68  tff(c_5930, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5922, c_879])).
% 7.26/2.68  tff(c_5934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_5930])).
% 7.26/2.68  tff(c_5935, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3827])).
% 7.26/2.68  tff(c_526, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_496])).
% 7.26/2.68  tff(c_5964, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5935, c_526])).
% 7.26/2.68  tff(c_5997, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_529, c_5964])).
% 7.26/2.68  tff(c_6133, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5997, c_69])).
% 7.26/2.68  tff(c_70, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_64])).
% 7.26/2.68  tff(c_1400, plain, (![A_132, C_133, B_134]: (~r1_xboole_0(A_132, C_133) | ~r1_xboole_0(A_132, B_134) | r1_xboole_0(A_132, k2_xboole_0(B_134, C_133)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.26/2.68  tff(c_11462, plain, (![B_298, C_299, A_300]: (r1_xboole_0(k2_xboole_0(B_298, C_299), A_300) | ~r1_xboole_0(A_300, C_299) | ~r1_xboole_0(A_300, B_298))), inference(resolution, [status(thm)], [c_1400, c_8])).
% 7.26/2.68  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.26/2.68  tff(c_11483, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_11462, c_46])).
% 7.26/2.68  tff(c_11493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6133, c_70, c_11483])).
% 7.26/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/2.68  
% 7.26/2.68  Inference rules
% 7.26/2.68  ----------------------
% 7.26/2.68  #Ref     : 0
% 7.26/2.68  #Sup     : 2813
% 7.26/2.68  #Fact    : 0
% 7.26/2.68  #Define  : 0
% 7.26/2.68  #Split   : 2
% 7.26/2.68  #Chain   : 0
% 7.26/2.68  #Close   : 0
% 7.26/2.68  
% 7.67/2.68  Ordering : KBO
% 7.67/2.68  
% 7.67/2.68  Simplification rules
% 7.67/2.68  ----------------------
% 7.67/2.68  #Subsume      : 100
% 7.67/2.68  #Demod        : 2275
% 7.67/2.68  #Tautology    : 1965
% 7.67/2.68  #SimpNegUnit  : 13
% 7.67/2.68  #BackRed      : 7
% 7.67/2.68  
% 7.67/2.68  #Partial instantiations: 0
% 7.67/2.68  #Strategies tried      : 1
% 7.67/2.68  
% 7.67/2.68  Timing (in seconds)
% 7.67/2.68  ----------------------
% 7.67/2.68  Preprocessing        : 0.29
% 7.67/2.68  Parsing              : 0.15
% 7.67/2.68  CNF conversion       : 0.02
% 7.67/2.68  Main loop            : 1.59
% 7.67/2.68  Inferencing          : 0.43
% 7.67/2.68  Reduction            : 0.74
% 7.67/2.68  Demodulation         : 0.60
% 7.67/2.68  BG Simplification    : 0.05
% 7.67/2.68  Subsumption          : 0.26
% 7.67/2.68  Abstraction          : 0.06
% 7.67/2.68  MUC search           : 0.00
% 7.67/2.68  Cooper               : 0.00
% 7.67/2.68  Total                : 1.91
% 7.67/2.68  Index Insertion      : 0.00
% 7.67/2.68  Index Deletion       : 0.00
% 7.67/2.68  Index Matching       : 0.00
% 7.67/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
