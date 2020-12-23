%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:53 EST 2020

% Result     : Theorem 9.19s
% Output     : CNFRefutation 9.37s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_113,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_94,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

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

tff(c_86,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,(
    ! [A_85,B_86] :
      ( r1_xboole_0(k1_tarski(A_85),B_86)
      | r2_hidden(A_85,B_86) ) ),
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
    ! [A_119,B_120] : k3_tarski(k2_tarski(A_119,B_120)) = k2_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_316,plain,(
    ! [A_124,B_125] : k3_tarski(k2_tarski(A_124,B_125)) = k2_xboole_0(B_125,A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_252])).

tff(c_80,plain,(
    ! [A_87,B_88] : k3_tarski(k2_tarski(A_87,B_88)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_322,plain,(
    ! [B_125,A_124] : k2_xboole_0(B_125,A_124) = k2_xboole_0(A_124,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_80])).

tff(c_663,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(k2_xboole_0(A_145,B_146),B_146) = A_145
      | ~ r1_xboole_0(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2437,plain,(
    ! [B_247,A_248] :
      ( k4_xboole_0(k2_xboole_0(B_247,A_248),B_247) = A_248
      | ~ r1_xboole_0(A_248,B_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_663])).

tff(c_2492,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13)
      | ~ r1_xboole_0(k4_xboole_0(B_14,A_13),A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2437])).

tff(c_2523,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2492])).

tff(c_692,plain,(
    ! [B_125,A_124] :
      ( k4_xboole_0(k2_xboole_0(B_125,A_124),B_125) = A_124
      | ~ r1_xboole_0(A_124,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_663])).

tff(c_2619,plain,(
    ! [A_255,B_256] :
      ( k4_xboole_0(A_255,B_256) = A_255
      | ~ r1_xboole_0(A_255,B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_692])).

tff(c_14638,plain,(
    ! [A_22413,B_22414] :
      ( k4_xboole_0(k1_tarski(A_22413),B_22414) = k1_tarski(A_22413)
      | r2_hidden(A_22413,B_22414) ) ),
    inference(resolution,[status(thm)],[c_78,c_2619])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_14744,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14638,c_169])).

tff(c_14808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_14744])).

tff(c_14809,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_64,plain,(
    ! [A_57] : k2_tarski(A_57,A_57) = k1_tarski(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14855,plain,(
    ! [A_22593,B_22594] : k1_enumset1(A_22593,A_22593,B_22594) = k2_tarski(A_22593,B_22594) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [E_38,A_32,C_34] : r2_hidden(E_38,k1_enumset1(A_32,E_38,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14873,plain,(
    ! [A_22595,B_22596] : r2_hidden(A_22595,k2_tarski(A_22595,B_22596)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14855,c_38])).

tff(c_14882,plain,(
    ! [A_57] : r2_hidden(A_57,k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14873])).

tff(c_14810,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14966,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14810,c_88])).

tff(c_14970,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14966,c_22])).

tff(c_15524,plain,(
    ! [A_22637,B_22638,C_22639] :
      ( ~ r1_xboole_0(A_22637,B_22638)
      | ~ r2_hidden(C_22639,B_22638)
      | ~ r2_hidden(C_22639,A_22637) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15651,plain,(
    ! [C_22645] :
      ( ~ r2_hidden(C_22645,'#skF_7')
      | ~ r2_hidden(C_22645,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_14970,c_15524])).

tff(c_15663,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_14882,c_15651])).

tff(c_15669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_15663])).

tff(c_15670,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_15709,plain,(
    ! [A_22659,B_22660] : k1_enumset1(A_22659,A_22659,B_22660) = k2_tarski(A_22659,B_22660) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_15727,plain,(
    ! [A_22661,B_22662] : r2_hidden(A_22661,k2_tarski(A_22661,B_22662)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15709,c_40])).

tff(c_15736,plain,(
    ! [A_57] : r2_hidden(A_57,k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_15727])).

tff(c_15671,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_15738,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15671,c_90])).

tff(c_15742,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15738,c_22])).

tff(c_16376,plain,(
    ! [A_22703,B_22704,C_22705] :
      ( ~ r1_xboole_0(A_22703,B_22704)
      | ~ r2_hidden(C_22705,B_22704)
      | ~ r2_hidden(C_22705,A_22703) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16503,plain,(
    ! [C_22711] :
      ( ~ r2_hidden(C_22711,'#skF_7')
      | ~ r2_hidden(C_22711,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_15742,c_16376])).

tff(c_16515,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_15736,c_16503])).

tff(c_16521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15670,c_16515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.19/3.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.21  
% 9.29/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.21  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 9.29/3.21  
% 9.29/3.21  %Foreground sorts:
% 9.29/3.21  
% 9.29/3.21  
% 9.29/3.21  %Background operators:
% 9.29/3.21  
% 9.29/3.21  
% 9.29/3.21  %Foreground operators:
% 9.29/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.29/3.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.29/3.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.29/3.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.29/3.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.29/3.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.29/3.21  tff('#skF_7', type, '#skF_7': $i).
% 9.29/3.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.29/3.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.29/3.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.29/3.21  tff('#skF_5', type, '#skF_5': $i).
% 9.29/3.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.29/3.21  tff('#skF_6', type, '#skF_6': $i).
% 9.29/3.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.29/3.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.29/3.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.29/3.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.29/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.29/3.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.29/3.21  tff('#skF_4', type, '#skF_4': $i).
% 9.29/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.29/3.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.29/3.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.29/3.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.29/3.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.29/3.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.29/3.21  
% 9.37/3.22  tff(f_121, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 9.37/3.22  tff(f_111, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.37/3.22  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.37/3.22  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.37/3.22  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.37/3.22  tff(f_113, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.37/3.22  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 9.37/3.22  tff(f_94, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.37/3.22  tff(f_96, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.37/3.22  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 9.37/3.22  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.37/3.22  tff(c_86, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.37/3.22  tff(c_168, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 9.37/3.22  tff(c_78, plain, (![A_85, B_86]: (r1_xboole_0(k1_tarski(A_85), B_86) | r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.37/3.22  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.37/3.22  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.37/3.22  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.37/3.22  tff(c_252, plain, (![A_119, B_120]: (k3_tarski(k2_tarski(A_119, B_120))=k2_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.37/3.22  tff(c_316, plain, (![A_124, B_125]: (k3_tarski(k2_tarski(A_124, B_125))=k2_xboole_0(B_125, A_124))), inference(superposition, [status(thm), theory('equality')], [c_32, c_252])).
% 9.37/3.22  tff(c_80, plain, (![A_87, B_88]: (k3_tarski(k2_tarski(A_87, B_88))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.37/3.22  tff(c_322, plain, (![B_125, A_124]: (k2_xboole_0(B_125, A_124)=k2_xboole_0(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_316, c_80])).
% 9.37/3.22  tff(c_663, plain, (![A_145, B_146]: (k4_xboole_0(k2_xboole_0(A_145, B_146), B_146)=A_145 | ~r1_xboole_0(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.37/3.22  tff(c_2437, plain, (![B_247, A_248]: (k4_xboole_0(k2_xboole_0(B_247, A_248), B_247)=A_248 | ~r1_xboole_0(A_248, B_247))), inference(superposition, [status(thm), theory('equality')], [c_322, c_663])).
% 9.37/3.22  tff(c_2492, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13) | ~r1_xboole_0(k4_xboole_0(B_14, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2437])).
% 9.37/3.22  tff(c_2523, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2492])).
% 9.37/3.22  tff(c_692, plain, (![B_125, A_124]: (k4_xboole_0(k2_xboole_0(B_125, A_124), B_125)=A_124 | ~r1_xboole_0(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_322, c_663])).
% 9.37/3.22  tff(c_2619, plain, (![A_255, B_256]: (k4_xboole_0(A_255, B_256)=A_255 | ~r1_xboole_0(A_255, B_256))), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_692])).
% 9.37/3.22  tff(c_14638, plain, (![A_22413, B_22414]: (k4_xboole_0(k1_tarski(A_22413), B_22414)=k1_tarski(A_22413) | r2_hidden(A_22413, B_22414))), inference(resolution, [status(thm)], [c_78, c_2619])).
% 9.37/3.22  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.37/3.22  tff(c_169, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 9.37/3.22  tff(c_14744, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14638, c_169])).
% 9.37/3.22  tff(c_14808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_14744])).
% 9.37/3.22  tff(c_14809, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 9.37/3.22  tff(c_64, plain, (![A_57]: (k2_tarski(A_57, A_57)=k1_tarski(A_57))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.37/3.22  tff(c_14855, plain, (![A_22593, B_22594]: (k1_enumset1(A_22593, A_22593, B_22594)=k2_tarski(A_22593, B_22594))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.37/3.22  tff(c_38, plain, (![E_38, A_32, C_34]: (r2_hidden(E_38, k1_enumset1(A_32, E_38, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.37/3.22  tff(c_14873, plain, (![A_22595, B_22596]: (r2_hidden(A_22595, k2_tarski(A_22595, B_22596)))), inference(superposition, [status(thm), theory('equality')], [c_14855, c_38])).
% 9.37/3.22  tff(c_14882, plain, (![A_57]: (r2_hidden(A_57, k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_14873])).
% 9.37/3.22  tff(c_14810, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 9.37/3.22  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.37/3.22  tff(c_14966, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14810, c_88])).
% 9.37/3.22  tff(c_14970, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14966, c_22])).
% 9.37/3.22  tff(c_15524, plain, (![A_22637, B_22638, C_22639]: (~r1_xboole_0(A_22637, B_22638) | ~r2_hidden(C_22639, B_22638) | ~r2_hidden(C_22639, A_22637))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.37/3.22  tff(c_15651, plain, (![C_22645]: (~r2_hidden(C_22645, '#skF_7') | ~r2_hidden(C_22645, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_14970, c_15524])).
% 9.37/3.22  tff(c_15663, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_14882, c_15651])).
% 9.37/3.22  tff(c_15669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14809, c_15663])).
% 9.37/3.22  tff(c_15670, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 9.37/3.22  tff(c_15709, plain, (![A_22659, B_22660]: (k1_enumset1(A_22659, A_22659, B_22660)=k2_tarski(A_22659, B_22660))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.37/3.22  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.37/3.22  tff(c_15727, plain, (![A_22661, B_22662]: (r2_hidden(A_22661, k2_tarski(A_22661, B_22662)))), inference(superposition, [status(thm), theory('equality')], [c_15709, c_40])).
% 9.37/3.22  tff(c_15736, plain, (![A_57]: (r2_hidden(A_57, k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_15727])).
% 9.37/3.22  tff(c_15671, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 9.37/3.22  tff(c_90, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.37/3.22  tff(c_15738, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_15671, c_90])).
% 9.37/3.22  tff(c_15742, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15738, c_22])).
% 9.37/3.22  tff(c_16376, plain, (![A_22703, B_22704, C_22705]: (~r1_xboole_0(A_22703, B_22704) | ~r2_hidden(C_22705, B_22704) | ~r2_hidden(C_22705, A_22703))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.37/3.22  tff(c_16503, plain, (![C_22711]: (~r2_hidden(C_22711, '#skF_7') | ~r2_hidden(C_22711, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_15742, c_16376])).
% 9.37/3.22  tff(c_16515, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_15736, c_16503])).
% 9.37/3.22  tff(c_16521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15670, c_16515])).
% 9.37/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.22  
% 9.37/3.22  Inference rules
% 9.37/3.22  ----------------------
% 9.37/3.22  #Ref     : 0
% 9.37/3.22  #Sup     : 3495
% 9.37/3.22  #Fact    : 18
% 9.37/3.22  #Define  : 0
% 9.37/3.22  #Split   : 2
% 9.37/3.22  #Chain   : 0
% 9.37/3.22  #Close   : 0
% 9.37/3.22  
% 9.37/3.22  Ordering : KBO
% 9.37/3.22  
% 9.37/3.22  Simplification rules
% 9.37/3.22  ----------------------
% 9.37/3.22  #Subsume      : 274
% 9.37/3.22  #Demod        : 3243
% 9.37/3.22  #Tautology    : 1938
% 9.37/3.22  #SimpNegUnit  : 11
% 9.37/3.22  #BackRed      : 4
% 9.37/3.22  
% 9.37/3.22  #Partial instantiations: 8442
% 9.37/3.22  #Strategies tried      : 1
% 9.37/3.22  
% 9.37/3.22  Timing (in seconds)
% 9.37/3.22  ----------------------
% 9.37/3.23  Preprocessing        : 0.37
% 9.37/3.23  Parsing              : 0.19
% 9.37/3.23  CNF conversion       : 0.03
% 9.37/3.23  Main loop            : 2.08
% 9.37/3.23  Inferencing          : 0.76
% 9.37/3.23  Reduction            : 0.90
% 9.37/3.23  Demodulation         : 0.78
% 9.37/3.23  BG Simplification    : 0.07
% 9.37/3.23  Subsumption          : 0.25
% 9.37/3.23  Abstraction          : 0.10
% 9.37/3.23  MUC search           : 0.00
% 9.37/3.23  Cooper               : 0.00
% 9.37/3.23  Total                : 2.48
% 9.37/3.23  Index Insertion      : 0.00
% 9.37/3.23  Index Deletion       : 0.00
% 9.37/3.23  Index Matching       : 0.00
% 9.37/3.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
