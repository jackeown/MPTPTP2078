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
% DateTime   : Thu Dec  3 09:55:56 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 134 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 193 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_756,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k3_subset_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_768,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_756])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_815,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_22])).

tff(c_822,plain,(
    ! [A_78,B_79] :
      ( k3_subset_1(A_78,k3_subset_1(A_78,B_79)) = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_831,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_822])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k3_subset_1(A_21,B_22),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3040,plain,(
    ! [A_157,B_158] :
      ( k4_xboole_0(A_157,k3_subset_1(A_157,B_158)) = k3_subset_1(A_157,k3_subset_1(A_157,B_158))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(resolution,[status(thm)],[c_28,c_756])).

tff(c_3046,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_3040])).

tff(c_3051,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_831,c_3046])).

tff(c_89,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    ! [A_33,B_34] : r1_tarski(k3_xboole_0(A_33,B_34),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_18])).

tff(c_3158,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3051,c_98])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_340,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_368,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ r1_tarski(A_60,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_340])).

tff(c_409,plain,(
    ! [B_61] : k3_xboole_0(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_368])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_424,plain,(
    ! [B_61] : k3_xboole_0(B_61,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_2])).

tff(c_559,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_568,plain,(
    ! [B_61] : k5_xboole_0(B_61,k1_xboole_0) = k4_xboole_0(B_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_559])).

tff(c_580,plain,(
    ! [B_61] : k5_xboole_0(B_61,k1_xboole_0) = B_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_568])).

tff(c_107,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_89])).

tff(c_508,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_107])).

tff(c_34,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2365,plain,(
    ! [A_145] :
      ( r1_xboole_0(A_145,'#skF_3')
      | ~ r1_tarski(A_145,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_12])).

tff(c_2440,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2365])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(A_16,k4_xboole_0(B_17,C_18))
      | ~ r1_xboole_0(A_16,C_18)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1728,plain,(
    ! [A_127,B_128] :
      ( k4_xboole_0(A_127,B_128) = A_127
      | ~ r1_tarski(A_127,k4_xboole_0(A_127,B_128)) ) ),
    inference(resolution,[status(thm)],[c_18,c_340])).

tff(c_1732,plain,(
    ! [B_17,C_18] :
      ( k4_xboole_0(B_17,C_18) = B_17
      | ~ r1_xboole_0(B_17,C_18)
      | ~ r1_tarski(B_17,B_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_1728])).

tff(c_1757,plain,(
    ! [B_17,C_18] :
      ( k4_xboole_0(B_17,C_18) = B_17
      | ~ r1_xboole_0(B_17,C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1732])).

tff(c_2448,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2440,c_1757])).

tff(c_2494,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2448,c_22])).

tff(c_2508,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_2,c_2494])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2547,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2508,c_10])).

tff(c_2566,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_2547])).

tff(c_255,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_xboole_0(A_49,C_50)
      | ~ r1_tarski(A_49,k4_xboole_0(B_51,C_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_298,plain,(
    ! [B_51,C_50] : r1_xboole_0(k4_xboole_0(B_51,C_50),C_50) ),
    inference(resolution,[status(thm)],[c_8,c_255])).

tff(c_2601,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2566,c_298])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_767,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_756])).

tff(c_961,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(A_87,k4_xboole_0(B_88,C_89))
      | ~ r1_xboole_0(A_87,C_89)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4043,plain,(
    ! [A_176] :
      ( r1_tarski(A_176,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_176,'#skF_2')
      | ~ r1_tarski(A_176,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_961])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4058,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_4043,c_32])).

tff(c_4066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3158,c_2601,c_4058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.91  
% 4.56/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.91  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.56/1.91  
% 4.56/1.91  %Foreground sorts:
% 4.56/1.91  
% 4.56/1.91  
% 4.56/1.91  %Background operators:
% 4.56/1.91  
% 4.56/1.91  
% 4.56/1.91  %Foreground operators:
% 4.56/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.56/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.56/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.56/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.91  
% 4.56/1.92  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 4.56/1.92  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.56/1.92  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.56/1.92  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.56/1.92  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.56/1.92  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.56/1.92  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.56/1.92  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.56/1.92  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.56/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.56/1.92  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.56/1.92  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.56/1.92  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.56/1.92  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.92  tff(c_756, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k3_subset_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.92  tff(c_768, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_756])).
% 4.56/1.92  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.92  tff(c_815, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_768, c_22])).
% 4.56/1.92  tff(c_822, plain, (![A_78, B_79]: (k3_subset_1(A_78, k3_subset_1(A_78, B_79))=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.56/1.92  tff(c_831, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_36, c_822])).
% 4.56/1.92  tff(c_28, plain, (![A_21, B_22]: (m1_subset_1(k3_subset_1(A_21, B_22), k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.56/1.92  tff(c_3040, plain, (![A_157, B_158]: (k4_xboole_0(A_157, k3_subset_1(A_157, B_158))=k3_subset_1(A_157, k3_subset_1(A_157, B_158)) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(resolution, [status(thm)], [c_28, c_756])).
% 4.56/1.92  tff(c_3046, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_3040])).
% 4.56/1.92  tff(c_3051, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_815, c_831, c_3046])).
% 4.56/1.92  tff(c_89, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.92  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.92  tff(c_98, plain, (![A_33, B_34]: (r1_tarski(k3_xboole_0(A_33, B_34), A_33))), inference(superposition, [status(thm), theory('equality')], [c_89, c_18])).
% 4.56/1.92  tff(c_3158, plain, (r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3051, c_98])).
% 4.56/1.92  tff(c_20, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.56/1.92  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.92  tff(c_340, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.56/1.92  tff(c_368, plain, (![A_60]: (k1_xboole_0=A_60 | ~r1_tarski(A_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_340])).
% 4.56/1.93  tff(c_409, plain, (![B_61]: (k3_xboole_0(k1_xboole_0, B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_98, c_368])).
% 4.56/1.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.93  tff(c_424, plain, (![B_61]: (k3_xboole_0(B_61, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_409, c_2])).
% 4.56/1.93  tff(c_559, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.56/1.93  tff(c_568, plain, (![B_61]: (k5_xboole_0(B_61, k1_xboole_0)=k4_xboole_0(B_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_424, c_559])).
% 4.56/1.93  tff(c_580, plain, (![B_61]: (k5_xboole_0(B_61, k1_xboole_0)=B_61)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_568])).
% 4.56/1.93  tff(c_107, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_89])).
% 4.56/1.93  tff(c_508, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_424, c_107])).
% 4.56/1.93  tff(c_34, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.93  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.56/1.93  tff(c_2365, plain, (![A_145]: (r1_xboole_0(A_145, '#skF_3') | ~r1_tarski(A_145, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_768, c_12])).
% 4.56/1.93  tff(c_2440, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_2365])).
% 4.56/1.93  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.56/1.93  tff(c_24, plain, (![A_16, B_17, C_18]: (r1_tarski(A_16, k4_xboole_0(B_17, C_18)) | ~r1_xboole_0(A_16, C_18) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.56/1.93  tff(c_1728, plain, (![A_127, B_128]: (k4_xboole_0(A_127, B_128)=A_127 | ~r1_tarski(A_127, k4_xboole_0(A_127, B_128)))), inference(resolution, [status(thm)], [c_18, c_340])).
% 4.56/1.93  tff(c_1732, plain, (![B_17, C_18]: (k4_xboole_0(B_17, C_18)=B_17 | ~r1_xboole_0(B_17, C_18) | ~r1_tarski(B_17, B_17))), inference(resolution, [status(thm)], [c_24, c_1728])).
% 4.56/1.93  tff(c_1757, plain, (![B_17, C_18]: (k4_xboole_0(B_17, C_18)=B_17 | ~r1_xboole_0(B_17, C_18))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1732])).
% 4.56/1.93  tff(c_2448, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_2440, c_1757])).
% 4.56/1.93  tff(c_2494, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2448, c_22])).
% 4.56/1.93  tff(c_2508, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_508, c_2, c_2494])).
% 4.56/1.93  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.56/1.93  tff(c_2547, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2508, c_10])).
% 4.56/1.93  tff(c_2566, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_580, c_2547])).
% 4.56/1.93  tff(c_255, plain, (![A_49, C_50, B_51]: (r1_xboole_0(A_49, C_50) | ~r1_tarski(A_49, k4_xboole_0(B_51, C_50)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.56/1.93  tff(c_298, plain, (![B_51, C_50]: (r1_xboole_0(k4_xboole_0(B_51, C_50), C_50))), inference(resolution, [status(thm)], [c_8, c_255])).
% 4.56/1.93  tff(c_2601, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2566, c_298])).
% 4.56/1.93  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.93  tff(c_767, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_756])).
% 4.56/1.93  tff(c_961, plain, (![A_87, B_88, C_89]: (r1_tarski(A_87, k4_xboole_0(B_88, C_89)) | ~r1_xboole_0(A_87, C_89) | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.56/1.93  tff(c_4043, plain, (![A_176]: (r1_tarski(A_176, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_176, '#skF_2') | ~r1_tarski(A_176, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_767, c_961])).
% 4.56/1.93  tff(c_32, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.93  tff(c_4058, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_4043, c_32])).
% 4.56/1.93  tff(c_4066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3158, c_2601, c_4058])).
% 4.56/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.93  
% 4.56/1.93  Inference rules
% 4.56/1.93  ----------------------
% 4.56/1.93  #Ref     : 0
% 4.56/1.93  #Sup     : 950
% 4.56/1.93  #Fact    : 0
% 4.56/1.93  #Define  : 0
% 4.56/1.93  #Split   : 3
% 4.56/1.93  #Chain   : 0
% 4.56/1.93  #Close   : 0
% 4.56/1.93  
% 4.56/1.93  Ordering : KBO
% 4.56/1.93  
% 4.56/1.93  Simplification rules
% 4.56/1.93  ----------------------
% 4.56/1.93  #Subsume      : 33
% 4.56/1.93  #Demod        : 718
% 4.56/1.93  #Tautology    : 575
% 4.56/1.93  #SimpNegUnit  : 0
% 4.56/1.93  #BackRed      : 7
% 4.56/1.93  
% 4.56/1.93  #Partial instantiations: 0
% 4.56/1.93  #Strategies tried      : 1
% 4.56/1.93  
% 4.56/1.93  Timing (in seconds)
% 4.56/1.93  ----------------------
% 4.56/1.93  Preprocessing        : 0.31
% 4.56/1.93  Parsing              : 0.17
% 4.56/1.93  CNF conversion       : 0.02
% 4.56/1.93  Main loop            : 0.82
% 4.56/1.93  Inferencing          : 0.24
% 4.56/1.93  Reduction            : 0.35
% 4.56/1.93  Demodulation         : 0.28
% 4.56/1.93  BG Simplification    : 0.03
% 4.56/1.93  Subsumption          : 0.14
% 4.56/1.93  Abstraction          : 0.03
% 4.56/1.93  MUC search           : 0.00
% 4.56/1.93  Cooper               : 0.00
% 4.56/1.93  Total                : 1.16
% 4.56/1.93  Index Insertion      : 0.00
% 4.56/1.93  Index Deletion       : 0.00
% 4.56/1.93  Index Matching       : 0.00
% 4.56/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
