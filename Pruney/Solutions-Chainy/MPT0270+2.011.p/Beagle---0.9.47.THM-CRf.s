%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:54 EST 2020

% Result     : Theorem 9.33s
% Output     : CNFRefutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 116 expanded)
%              Number of leaves         :   37 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 141 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_113,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_94,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_86,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,(
    ! [A_86,B_87] :
      ( r1_xboole_0(k1_tarski(A_86),B_87)
      | r2_hidden(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_252,plain,(
    ! [A_120,B_121] : k3_tarski(k2_tarski(A_120,B_121)) = k2_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_299,plain,(
    ! [A_125,B_126] : k3_tarski(k2_tarski(A_125,B_126)) = k2_xboole_0(B_126,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_252])).

tff(c_80,plain,(
    ! [A_88,B_89] : k3_tarski(k2_tarski(A_88,B_89)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_305,plain,(
    ! [B_126,A_125] : k2_xboole_0(B_126,A_125) = k2_xboole_0(A_125,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_80])).

tff(c_541,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(k2_xboole_0(A_142,B_143),B_143) = A_142
      | ~ r1_xboole_0(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2347,plain,(
    ! [A_250,B_251] :
      ( k4_xboole_0(k2_xboole_0(A_250,B_251),A_250) = B_251
      | ~ r1_xboole_0(B_251,A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_541])).

tff(c_2417,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13)
      | ~ r1_xboole_0(k4_xboole_0(B_14,A_13),A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2347])).

tff(c_2436,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2417])).

tff(c_573,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(k2_xboole_0(A_125,B_126),A_125) = B_126
      | ~ r1_xboole_0(B_126,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_541])).

tff(c_2528,plain,(
    ! [B_254,A_255] :
      ( k4_xboole_0(B_254,A_255) = B_254
      | ~ r1_xboole_0(B_254,A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_573])).

tff(c_14771,plain,(
    ! [A_22582,B_22583] :
      ( k4_xboole_0(k1_tarski(A_22582),B_22583) = k1_tarski(A_22582)
      | r2_hidden(A_22582,B_22583) ) ),
    inference(resolution,[status(thm)],[c_78,c_2528])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_14862,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14771,c_169])).

tff(c_14922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_14862])).

tff(c_14923,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_64,plain,(
    ! [A_58] : k2_tarski(A_58,A_58) = k1_tarski(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14969,plain,(
    ! [A_22762,B_22763] : k1_enumset1(A_22762,A_22762,B_22763) = k2_tarski(A_22762,B_22763) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [E_38,A_32,C_34] : r2_hidden(E_38,k1_enumset1(A_32,E_38,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14987,plain,(
    ! [A_22764,B_22765] : r2_hidden(A_22764,k2_tarski(A_22764,B_22765)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14969,c_38])).

tff(c_14996,plain,(
    ! [A_58] : r2_hidden(A_58,k1_tarski(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14987])).

tff(c_14924,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_15080,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14924,c_88])).

tff(c_15084,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15080,c_22])).

tff(c_15389,plain,(
    ! [A_22793,B_22794,C_22795] :
      ( ~ r1_xboole_0(A_22793,B_22794)
      | ~ r2_hidden(C_22795,B_22794)
      | ~ r2_hidden(C_22795,A_22793) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15507,plain,(
    ! [C_22801] :
      ( ~ r2_hidden(C_22801,'#skF_7')
      | ~ r2_hidden(C_22801,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_15084,c_15389])).

tff(c_15519,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_14996,c_15507])).

tff(c_15525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14923,c_15519])).

tff(c_15526,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_15565,plain,(
    ! [A_22815,B_22816] : k1_enumset1(A_22815,A_22815,B_22816) = k2_tarski(A_22815,B_22816) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_15583,plain,(
    ! [A_22817,B_22818] : r2_hidden(A_22817,k2_tarski(A_22817,B_22818)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15565,c_40])).

tff(c_15592,plain,(
    ! [A_58] : r2_hidden(A_58,k1_tarski(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_15583])).

tff(c_15527,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_15594,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15527,c_90])).

tff(c_15598,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15594,c_22])).

tff(c_16066,plain,(
    ! [A_22854,B_22855,C_22856] :
      ( ~ r1_xboole_0(A_22854,B_22855)
      | ~ r2_hidden(C_22856,B_22855)
      | ~ r2_hidden(C_22856,A_22854) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16287,plain,(
    ! [C_22864] :
      ( ~ r2_hidden(C_22864,'#skF_7')
      | ~ r2_hidden(C_22864,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_15598,c_16066])).

tff(c_16299,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_15592,c_16287])).

tff(c_16305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15526,c_16299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n016.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 14:13:19 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.33/3.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.24  
% 9.33/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.25  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 9.33/3.25  
% 9.33/3.25  %Foreground sorts:
% 9.33/3.25  
% 9.33/3.25  
% 9.33/3.25  %Background operators:
% 9.33/3.25  
% 9.33/3.25  
% 9.33/3.25  %Foreground operators:
% 9.33/3.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.33/3.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.33/3.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.33/3.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.33/3.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.33/3.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.33/3.25  tff('#skF_7', type, '#skF_7': $i).
% 9.33/3.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.33/3.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.33/3.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.33/3.25  tff('#skF_5', type, '#skF_5': $i).
% 9.33/3.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.33/3.25  tff('#skF_6', type, '#skF_6': $i).
% 9.33/3.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.33/3.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.33/3.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.33/3.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.33/3.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.33/3.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.33/3.25  tff('#skF_4', type, '#skF_4': $i).
% 9.33/3.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.33/3.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.33/3.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.33/3.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.33/3.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.33/3.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.33/3.25  
% 9.33/3.26  tff(f_121, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 9.33/3.26  tff(f_111, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.33/3.26  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.33/3.26  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.33/3.26  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.33/3.26  tff(f_113, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.33/3.26  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 9.33/3.26  tff(f_94, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.33/3.26  tff(f_96, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.33/3.26  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.33/3.26  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.33/3.26  tff(c_86, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.33/3.26  tff(c_168, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 9.33/3.26  tff(c_78, plain, (![A_86, B_87]: (r1_xboole_0(k1_tarski(A_86), B_87) | r2_hidden(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.33/3.26  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.33/3.26  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.26  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.33/3.26  tff(c_252, plain, (![A_120, B_121]: (k3_tarski(k2_tarski(A_120, B_121))=k2_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.33/3.26  tff(c_299, plain, (![A_125, B_126]: (k3_tarski(k2_tarski(A_125, B_126))=k2_xboole_0(B_126, A_125))), inference(superposition, [status(thm), theory('equality')], [c_32, c_252])).
% 9.33/3.26  tff(c_80, plain, (![A_88, B_89]: (k3_tarski(k2_tarski(A_88, B_89))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.33/3.26  tff(c_305, plain, (![B_126, A_125]: (k2_xboole_0(B_126, A_125)=k2_xboole_0(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_299, c_80])).
% 9.33/3.26  tff(c_541, plain, (![A_142, B_143]: (k4_xboole_0(k2_xboole_0(A_142, B_143), B_143)=A_142 | ~r1_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.33/3.26  tff(c_2347, plain, (![A_250, B_251]: (k4_xboole_0(k2_xboole_0(A_250, B_251), A_250)=B_251 | ~r1_xboole_0(B_251, A_250))), inference(superposition, [status(thm), theory('equality')], [c_305, c_541])).
% 9.33/3.26  tff(c_2417, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13) | ~r1_xboole_0(k4_xboole_0(B_14, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2347])).
% 9.33/3.26  tff(c_2436, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2417])).
% 9.33/3.26  tff(c_573, plain, (![A_125, B_126]: (k4_xboole_0(k2_xboole_0(A_125, B_126), A_125)=B_126 | ~r1_xboole_0(B_126, A_125))), inference(superposition, [status(thm), theory('equality')], [c_305, c_541])).
% 9.33/3.26  tff(c_2528, plain, (![B_254, A_255]: (k4_xboole_0(B_254, A_255)=B_254 | ~r1_xboole_0(B_254, A_255))), inference(demodulation, [status(thm), theory('equality')], [c_2436, c_573])).
% 9.33/3.26  tff(c_14771, plain, (![A_22582, B_22583]: (k4_xboole_0(k1_tarski(A_22582), B_22583)=k1_tarski(A_22582) | r2_hidden(A_22582, B_22583))), inference(resolution, [status(thm)], [c_78, c_2528])).
% 9.33/3.26  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.33/3.26  tff(c_169, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 9.33/3.26  tff(c_14862, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14771, c_169])).
% 9.33/3.26  tff(c_14922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_14862])).
% 9.33/3.26  tff(c_14923, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 9.33/3.26  tff(c_64, plain, (![A_58]: (k2_tarski(A_58, A_58)=k1_tarski(A_58))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.33/3.26  tff(c_14969, plain, (![A_22762, B_22763]: (k1_enumset1(A_22762, A_22762, B_22763)=k2_tarski(A_22762, B_22763))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.33/3.26  tff(c_38, plain, (![E_38, A_32, C_34]: (r2_hidden(E_38, k1_enumset1(A_32, E_38, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.33/3.26  tff(c_14987, plain, (![A_22764, B_22765]: (r2_hidden(A_22764, k2_tarski(A_22764, B_22765)))), inference(superposition, [status(thm), theory('equality')], [c_14969, c_38])).
% 9.33/3.26  tff(c_14996, plain, (![A_58]: (r2_hidden(A_58, k1_tarski(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_14987])).
% 9.33/3.26  tff(c_14924, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 9.33/3.26  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.33/3.26  tff(c_15080, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14924, c_88])).
% 9.33/3.26  tff(c_15084, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15080, c_22])).
% 9.33/3.26  tff(c_15389, plain, (![A_22793, B_22794, C_22795]: (~r1_xboole_0(A_22793, B_22794) | ~r2_hidden(C_22795, B_22794) | ~r2_hidden(C_22795, A_22793))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.33/3.26  tff(c_15507, plain, (![C_22801]: (~r2_hidden(C_22801, '#skF_7') | ~r2_hidden(C_22801, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_15084, c_15389])).
% 9.33/3.26  tff(c_15519, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_14996, c_15507])).
% 9.33/3.26  tff(c_15525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14923, c_15519])).
% 9.33/3.26  tff(c_15526, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 9.33/3.26  tff(c_15565, plain, (![A_22815, B_22816]: (k1_enumset1(A_22815, A_22815, B_22816)=k2_tarski(A_22815, B_22816))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.33/3.26  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.33/3.26  tff(c_15583, plain, (![A_22817, B_22818]: (r2_hidden(A_22817, k2_tarski(A_22817, B_22818)))), inference(superposition, [status(thm), theory('equality')], [c_15565, c_40])).
% 9.33/3.26  tff(c_15592, plain, (![A_58]: (r2_hidden(A_58, k1_tarski(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_15583])).
% 9.33/3.26  tff(c_15527, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 9.33/3.26  tff(c_90, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.33/3.26  tff(c_15594, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_15527, c_90])).
% 9.33/3.26  tff(c_15598, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15594, c_22])).
% 9.33/3.26  tff(c_16066, plain, (![A_22854, B_22855, C_22856]: (~r1_xboole_0(A_22854, B_22855) | ~r2_hidden(C_22856, B_22855) | ~r2_hidden(C_22856, A_22854))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.33/3.26  tff(c_16287, plain, (![C_22864]: (~r2_hidden(C_22864, '#skF_7') | ~r2_hidden(C_22864, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_15598, c_16066])).
% 9.33/3.26  tff(c_16299, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_15592, c_16287])).
% 9.33/3.26  tff(c_16305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15526, c_16299])).
% 9.33/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.26  
% 9.33/3.26  Inference rules
% 9.33/3.26  ----------------------
% 9.33/3.26  #Ref     : 0
% 9.33/3.26  #Sup     : 3447
% 9.33/3.26  #Fact    : 18
% 9.33/3.26  #Define  : 0
% 9.33/3.26  #Split   : 2
% 9.33/3.26  #Chain   : 0
% 9.33/3.26  #Close   : 0
% 9.33/3.26  
% 9.33/3.26  Ordering : KBO
% 9.33/3.26  
% 9.33/3.26  Simplification rules
% 9.33/3.26  ----------------------
% 9.33/3.26  #Subsume      : 272
% 9.33/3.26  #Demod        : 3068
% 9.33/3.26  #Tautology    : 1949
% 9.33/3.26  #SimpNegUnit  : 11
% 9.33/3.26  #BackRed      : 2
% 9.33/3.26  
% 9.33/3.26  #Partial instantiations: 8505
% 9.33/3.26  #Strategies tried      : 1
% 9.33/3.26  
% 9.33/3.26  Timing (in seconds)
% 9.33/3.26  ----------------------
% 9.33/3.26  Preprocessing        : 0.37
% 9.33/3.26  Parsing              : 0.19
% 9.33/3.26  CNF conversion       : 0.03
% 9.33/3.26  Main loop            : 2.16
% 9.33/3.26  Inferencing          : 0.80
% 9.33/3.26  Reduction            : 0.91
% 9.33/3.26  Demodulation         : 0.79
% 9.33/3.26  BG Simplification    : 0.08
% 9.33/3.26  Subsumption          : 0.26
% 9.33/3.26  Abstraction          : 0.11
% 9.33/3.26  MUC search           : 0.00
% 9.33/3.26  Cooper               : 0.00
% 9.33/3.26  Total                : 2.56
% 9.33/3.27  Index Insertion      : 0.00
% 9.33/3.27  Index Deletion       : 0.00
% 9.33/3.27  Index Matching       : 0.00
% 9.33/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
