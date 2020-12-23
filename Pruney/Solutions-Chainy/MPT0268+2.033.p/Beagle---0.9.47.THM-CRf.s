%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:38 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 100 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 127 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_145,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(k1_tarski(A_59),B_60)
      | r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [B_60,A_59] :
      ( r1_xboole_0(B_60,k1_tarski(A_59))
      | r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_145,c_4])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_440,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_768,plain,(
    ! [A_108,B_109] :
      ( ~ r1_xboole_0(A_108,B_109)
      | k3_xboole_0(A_108,B_109) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_440])).

tff(c_791,plain,(
    ! [B_60,A_59] :
      ( k3_xboole_0(B_60,k1_tarski(A_59)) = k1_xboole_0
      | r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_148,c_768])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1255,plain,(
    ! [A_129,B_130] : k3_xboole_0(k4_xboole_0(A_129,B_130),A_129) = k4_xboole_0(A_129,B_130) ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_1345,plain,(
    ! [A_1,B_130] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_130)) = k4_xboole_0(A_1,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1255])).

tff(c_22,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_240,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | k4_xboole_0(A_66,B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1191,plain,(
    ! [A_125,B_126] :
      ( k3_xboole_0(A_125,B_126) = A_125
      | k4_xboole_0(A_125,B_126) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_240,c_18])).

tff(c_1203,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = A_20
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1191])).

tff(c_5708,plain,(
    ! [A_190,B_191] :
      ( k4_xboole_0(A_190,B_191) = A_190
      | k3_xboole_0(A_190,B_191) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1203])).

tff(c_38,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_166,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_5896,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5708,c_166])).

tff(c_5922,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_5896])).

tff(c_5926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_5922])).

tff(c_5927,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_5928,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5937,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_6000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5928,c_5937])).

tff(c_6001,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6108,plain,(
    r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6001,c_24])).

tff(c_6130,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6108,c_4])).

tff(c_6262,plain,(
    ! [A_194,B_195] :
      ( ~ r2_hidden(A_194,B_195)
      | ~ r1_xboole_0(k1_tarski(A_194),B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6265,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6130,c_6262])).

tff(c_6283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5927,c_6265])).

tff(c_6284,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6285,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6291,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6285,c_44])).

tff(c_6298,plain,(
    r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6291,c_24])).

tff(c_6304,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6298,c_4])).

tff(c_6419,plain,(
    ! [A_204,B_205] :
      ( ~ r2_hidden(A_204,B_205)
      | ~ r1_xboole_0(k1_tarski(A_204),B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6426,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6304,c_6419])).

tff(c_6431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6284,c_6426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:46:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.93  
% 4.70/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.93  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 4.70/1.93  
% 4.70/1.93  %Foreground sorts:
% 4.70/1.93  
% 4.70/1.93  
% 4.70/1.93  %Background operators:
% 4.70/1.93  
% 4.70/1.93  
% 4.70/1.93  %Foreground operators:
% 4.70/1.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.70/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.70/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.70/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/1.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.70/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.70/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.70/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.70/1.93  tff('#skF_5', type, '#skF_5': $i).
% 4.70/1.93  tff('#skF_6', type, '#skF_6': $i).
% 4.70/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.70/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.70/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.93  tff('#skF_4', type, '#skF_4': $i).
% 4.70/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.70/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.70/1.93  
% 4.70/1.94  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.70/1.94  tff(f_87, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.70/1.94  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.70/1.94  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.70/1.94  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.70/1.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.70/1.94  tff(f_65, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.70/1.94  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.70/1.94  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.70/1.94  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.70/1.94  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.70/1.94  tff(f_82, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.70/1.94  tff(c_40, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.70/1.94  tff(c_57, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 4.70/1.94  tff(c_145, plain, (![A_59, B_60]: (r1_xboole_0(k1_tarski(A_59), B_60) | r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.70/1.94  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/1.94  tff(c_148, plain, (![B_60, A_59]: (r1_xboole_0(B_60, k1_tarski(A_59)) | r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_145, c_4])).
% 4.70/1.94  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.70/1.94  tff(c_440, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.70/1.94  tff(c_768, plain, (![A_108, B_109]: (~r1_xboole_0(A_108, B_109) | k3_xboole_0(A_108, B_109)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_440])).
% 4.70/1.94  tff(c_791, plain, (![B_60, A_59]: (k3_xboole_0(B_60, k1_tarski(A_59))=k1_xboole_0 | r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_148, c_768])).
% 4.70/1.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.70/1.94  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.70/1.94  tff(c_100, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.70/1.94  tff(c_1255, plain, (![A_129, B_130]: (k3_xboole_0(k4_xboole_0(A_129, B_130), A_129)=k4_xboole_0(A_129, B_130))), inference(resolution, [status(thm)], [c_20, c_100])).
% 4.70/1.94  tff(c_1345, plain, (![A_1, B_130]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_130))=k4_xboole_0(A_1, B_130))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1255])).
% 4.70/1.94  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.70/1.94  tff(c_240, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | k4_xboole_0(A_66, B_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.70/1.94  tff(c_18, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.70/1.94  tff(c_1191, plain, (![A_125, B_126]: (k3_xboole_0(A_125, B_126)=A_125 | k4_xboole_0(A_125, B_126)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_240, c_18])).
% 4.70/1.94  tff(c_1203, plain, (![A_20, B_21]: (k3_xboole_0(A_20, k4_xboole_0(A_20, B_21))=A_20 | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_1191])).
% 4.70/1.94  tff(c_5708, plain, (![A_190, B_191]: (k4_xboole_0(A_190, B_191)=A_190 | k3_xboole_0(A_190, B_191)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1203])).
% 4.70/1.94  tff(c_38, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.70/1.94  tff(c_166, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_38])).
% 4.70/1.94  tff(c_5896, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5708, c_166])).
% 4.70/1.94  tff(c_5922, plain, (r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_791, c_5896])).
% 4.70/1.94  tff(c_5926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_5922])).
% 4.70/1.94  tff(c_5927, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 4.70/1.94  tff(c_5928, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 4.70/1.94  tff(c_42, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.70/1.94  tff(c_5937, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_42])).
% 4.70/1.94  tff(c_6000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5928, c_5937])).
% 4.70/1.94  tff(c_6001, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 4.70/1.94  tff(c_24, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.70/1.94  tff(c_6108, plain, (r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6001, c_24])).
% 4.70/1.94  tff(c_6130, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_6108, c_4])).
% 4.70/1.94  tff(c_6262, plain, (![A_194, B_195]: (~r2_hidden(A_194, B_195) | ~r1_xboole_0(k1_tarski(A_194), B_195))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.70/1.94  tff(c_6265, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6130, c_6262])).
% 4.70/1.94  tff(c_6283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5927, c_6265])).
% 4.70/1.94  tff(c_6284, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 4.70/1.94  tff(c_6285, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 4.70/1.94  tff(c_44, plain, (~r2_hidden('#skF_4', '#skF_3') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.70/1.94  tff(c_6291, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6285, c_44])).
% 4.70/1.94  tff(c_6298, plain, (r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6291, c_24])).
% 4.70/1.94  tff(c_6304, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_6298, c_4])).
% 4.70/1.94  tff(c_6419, plain, (![A_204, B_205]: (~r2_hidden(A_204, B_205) | ~r1_xboole_0(k1_tarski(A_204), B_205))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.70/1.94  tff(c_6426, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6304, c_6419])).
% 4.70/1.94  tff(c_6431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6284, c_6426])).
% 4.70/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.94  
% 4.70/1.94  Inference rules
% 4.70/1.94  ----------------------
% 4.70/1.94  #Ref     : 0
% 4.70/1.94  #Sup     : 1598
% 4.70/1.94  #Fact    : 0
% 4.70/1.94  #Define  : 0
% 4.70/1.94  #Split   : 3
% 4.70/1.94  #Chain   : 0
% 4.70/1.94  #Close   : 0
% 4.70/1.94  
% 4.70/1.94  Ordering : KBO
% 4.70/1.94  
% 4.70/1.94  Simplification rules
% 4.70/1.94  ----------------------
% 4.70/1.94  #Subsume      : 97
% 4.70/1.94  #Demod        : 1699
% 4.70/1.94  #Tautology    : 1206
% 4.70/1.94  #SimpNegUnit  : 29
% 4.70/1.94  #BackRed      : 2
% 4.70/1.94  
% 4.70/1.94  #Partial instantiations: 0
% 4.70/1.94  #Strategies tried      : 1
% 4.70/1.94  
% 4.70/1.94  Timing (in seconds)
% 4.70/1.94  ----------------------
% 4.70/1.95  Preprocessing        : 0.31
% 4.70/1.95  Parsing              : 0.17
% 4.70/1.95  CNF conversion       : 0.02
% 4.70/1.95  Main loop            : 0.87
% 4.70/1.95  Inferencing          : 0.26
% 4.70/1.95  Reduction            : 0.41
% 4.70/1.95  Demodulation         : 0.34
% 4.70/1.95  BG Simplification    : 0.03
% 4.70/1.95  Subsumption          : 0.11
% 4.70/1.95  Abstraction          : 0.04
% 4.70/1.95  MUC search           : 0.00
% 4.70/1.95  Cooper               : 0.00
% 4.70/1.95  Total                : 1.21
% 4.70/1.95  Index Insertion      : 0.00
% 4.70/1.95  Index Deletion       : 0.00
% 4.70/1.95  Index Matching       : 0.00
% 4.70/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
