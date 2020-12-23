%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:50 EST 2020

% Result     : Theorem 8.39s
% Output     : CNFRefutation 8.39s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 102 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 165 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_60,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_114,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_193,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_245,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(B_76,A_77)
      | ~ m1_subset_1(B_76,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_249,plain,(
    ! [B_76,A_25] :
      ( r1_tarski(B_76,A_25)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_245,c_24])).

tff(c_253,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_249])).

tff(c_266,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_253])).

tff(c_553,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = k3_subset_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_570,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_553])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1911,plain,(
    ! [A_209] :
      ( r1_xboole_0(A_209,'#skF_4')
      | ~ r1_tarski(A_209,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_8])).

tff(c_1979,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_1911])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1986,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1979,c_4])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_569,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_553])).

tff(c_18,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_628,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_tarski(A_121,B_122)
      | ~ r1_xboole_0(A_121,C_123)
      | ~ r1_tarski(A_121,k2_xboole_0(B_122,C_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1713,plain,(
    ! [A_201,A_202,B_203] :
      ( r1_tarski(A_201,k3_xboole_0(A_202,B_203))
      | ~ r1_xboole_0(A_201,k4_xboole_0(A_202,B_203))
      | ~ r1_tarski(A_201,A_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_628])).

tff(c_8878,plain,(
    ! [A_559] :
      ( r1_tarski(A_559,k3_xboole_0('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_559,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_559,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_1713])).

tff(c_8916,plain,
    ( r1_tarski('#skF_4',k3_xboole_0('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1986,c_8878])).

tff(c_8952,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_8916])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_348,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_tarski(A_95,C_96)
      | ~ r1_tarski(B_97,C_96)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1030,plain,(
    ! [A_161,A_162,B_163] :
      ( r1_tarski(A_161,A_162)
      | ~ r1_tarski(A_161,k3_xboole_0(A_162,B_163)) ) ),
    inference(resolution,[status(thm)],[c_12,c_348])).

tff(c_1057,plain,(
    ! [A_161,A_1,B_2] :
      ( r1_tarski(A_161,A_1)
      | ~ r1_tarski(A_161,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1030])).

tff(c_8973,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8952,c_1057])).

tff(c_8987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_8973])).

tff(c_8988,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_9004,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8988,c_54])).

tff(c_9311,plain,(
    ! [A_614,B_615] :
      ( k4_xboole_0(A_614,B_615) = k3_subset_1(A_614,B_615)
      | ~ m1_subset_1(B_615,k1_zfmisc_1(A_614)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_9328,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_9311])).

tff(c_9327,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_9311])).

tff(c_9469,plain,(
    ! [C_622,B_623,A_624] :
      ( r1_tarski(k4_xboole_0(C_622,B_623),k4_xboole_0(C_622,A_624))
      | ~ r1_tarski(A_624,B_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_11123,plain,(
    ! [A_741] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',A_741))
      | ~ r1_tarski(A_741,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9327,c_9469])).

tff(c_11136,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9328,c_11123])).

tff(c_11146,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8988,c_11136])).

tff(c_11148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9004,c_11146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.39/3.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.39/3.15  
% 8.39/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.39/3.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.39/3.15  
% 8.39/3.15  %Foreground sorts:
% 8.39/3.15  
% 8.39/3.15  
% 8.39/3.15  %Background operators:
% 8.39/3.15  
% 8.39/3.15  
% 8.39/3.15  %Foreground operators:
% 8.39/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.39/3.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.39/3.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.39/3.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.39/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.39/3.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.39/3.15  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.39/3.15  tff('#skF_5', type, '#skF_5': $i).
% 8.39/3.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.39/3.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.39/3.15  tff('#skF_3', type, '#skF_3': $i).
% 8.39/3.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.39/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.39/3.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.39/3.15  tff('#skF_4', type, '#skF_4': $i).
% 8.39/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.39/3.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.39/3.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.39/3.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.39/3.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.39/3.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.39/3.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.39/3.15  
% 8.39/3.16  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 8.39/3.16  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.39/3.16  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.39/3.16  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.39/3.16  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.39/3.16  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 8.39/3.16  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.39/3.16  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.39/3.16  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 8.39/3.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.39/3.16  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.39/3.16  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.39/3.16  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 8.39/3.16  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.39/3.16  tff(c_114, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_60])).
% 8.39/3.16  tff(c_54, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.39/3.16  tff(c_193, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_54])).
% 8.39/3.16  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.39/3.16  tff(c_48, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.39/3.16  tff(c_245, plain, (![B_76, A_77]: (r2_hidden(B_76, A_77) | ~m1_subset_1(B_76, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.39/3.16  tff(c_24, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.39/3.16  tff(c_249, plain, (![B_76, A_25]: (r1_tarski(B_76, A_25) | ~m1_subset_1(B_76, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_245, c_24])).
% 8.39/3.16  tff(c_253, plain, (![B_78, A_79]: (r1_tarski(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)))), inference(negUnitSimplification, [status(thm)], [c_48, c_249])).
% 8.39/3.16  tff(c_266, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_253])).
% 8.39/3.16  tff(c_553, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=k3_subset_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.39/3.16  tff(c_570, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_553])).
% 8.39/3.16  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.39/3.16  tff(c_1911, plain, (![A_209]: (r1_xboole_0(A_209, '#skF_4') | ~r1_tarski(A_209, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_570, c_8])).
% 8.39/3.16  tff(c_1979, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_114, c_1911])).
% 8.39/3.16  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.39/3.16  tff(c_1986, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_1979, c_4])).
% 8.39/3.16  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.39/3.16  tff(c_569, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_553])).
% 8.39/3.16  tff(c_18, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.39/3.16  tff(c_628, plain, (![A_121, B_122, C_123]: (r1_tarski(A_121, B_122) | ~r1_xboole_0(A_121, C_123) | ~r1_tarski(A_121, k2_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.39/3.16  tff(c_1713, plain, (![A_201, A_202, B_203]: (r1_tarski(A_201, k3_xboole_0(A_202, B_203)) | ~r1_xboole_0(A_201, k4_xboole_0(A_202, B_203)) | ~r1_tarski(A_201, A_202))), inference(superposition, [status(thm), theory('equality')], [c_18, c_628])).
% 8.39/3.16  tff(c_8878, plain, (![A_559]: (r1_tarski(A_559, k3_xboole_0('#skF_3', '#skF_5')) | ~r1_xboole_0(A_559, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_559, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_1713])).
% 8.39/3.16  tff(c_8916, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1986, c_8878])).
% 8.39/3.16  tff(c_8952, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_8916])).
% 8.39/3.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.39/3.16  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.39/3.16  tff(c_348, plain, (![A_95, C_96, B_97]: (r1_tarski(A_95, C_96) | ~r1_tarski(B_97, C_96) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.39/3.16  tff(c_1030, plain, (![A_161, A_162, B_163]: (r1_tarski(A_161, A_162) | ~r1_tarski(A_161, k3_xboole_0(A_162, B_163)))), inference(resolution, [status(thm)], [c_12, c_348])).
% 8.39/3.16  tff(c_1057, plain, (![A_161, A_1, B_2]: (r1_tarski(A_161, A_1) | ~r1_tarski(A_161, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1030])).
% 8.39/3.16  tff(c_8973, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8952, c_1057])).
% 8.39/3.16  tff(c_8987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_8973])).
% 8.39/3.16  tff(c_8988, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 8.39/3.16  tff(c_9004, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8988, c_54])).
% 8.39/3.16  tff(c_9311, plain, (![A_614, B_615]: (k4_xboole_0(A_614, B_615)=k3_subset_1(A_614, B_615) | ~m1_subset_1(B_615, k1_zfmisc_1(A_614)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.39/3.16  tff(c_9328, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_9311])).
% 8.39/3.16  tff(c_9327, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_9311])).
% 8.39/3.16  tff(c_9469, plain, (![C_622, B_623, A_624]: (r1_tarski(k4_xboole_0(C_622, B_623), k4_xboole_0(C_622, A_624)) | ~r1_tarski(A_624, B_623))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.39/3.16  tff(c_11123, plain, (![A_741]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', A_741)) | ~r1_tarski(A_741, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9327, c_9469])).
% 8.39/3.16  tff(c_11136, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9328, c_11123])).
% 8.39/3.16  tff(c_11146, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8988, c_11136])).
% 8.39/3.16  tff(c_11148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9004, c_11146])).
% 8.39/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.39/3.16  
% 8.39/3.16  Inference rules
% 8.39/3.16  ----------------------
% 8.39/3.16  #Ref     : 0
% 8.39/3.16  #Sup     : 2450
% 8.39/3.16  #Fact    : 0
% 8.39/3.16  #Define  : 0
% 8.39/3.16  #Split   : 1
% 8.39/3.16  #Chain   : 0
% 8.39/3.16  #Close   : 0
% 8.39/3.16  
% 8.39/3.16  Ordering : KBO
% 8.39/3.16  
% 8.39/3.16  Simplification rules
% 8.39/3.16  ----------------------
% 8.39/3.16  #Subsume      : 61
% 8.39/3.16  #Demod        : 726
% 8.39/3.16  #Tautology    : 708
% 8.39/3.16  #SimpNegUnit  : 12
% 8.39/3.16  #BackRed      : 0
% 8.39/3.16  
% 8.39/3.16  #Partial instantiations: 0
% 8.39/3.16  #Strategies tried      : 1
% 8.39/3.16  
% 8.39/3.16  Timing (in seconds)
% 8.39/3.16  ----------------------
% 8.39/3.17  Preprocessing        : 0.33
% 8.39/3.17  Parsing              : 0.17
% 8.39/3.17  CNF conversion       : 0.02
% 8.39/3.17  Main loop            : 2.06
% 8.39/3.17  Inferencing          : 0.51
% 8.39/3.17  Reduction            : 0.88
% 8.39/3.17  Demodulation         : 0.71
% 8.39/3.17  BG Simplification    : 0.06
% 8.39/3.17  Subsumption          : 0.44
% 8.39/3.17  Abstraction          : 0.07
% 8.39/3.17  MUC search           : 0.00
% 8.39/3.17  Cooper               : 0.00
% 8.39/3.17  Total                : 2.42
% 8.39/3.17  Index Insertion      : 0.00
% 8.39/3.17  Index Deletion       : 0.00
% 8.39/3.17  Index Matching       : 0.00
% 8.39/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
