%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:26 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 114 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 137 expanded)
%              Number of equality atoms :   40 (  66 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_40,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_14,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_250,plain,(
    ! [B_66,A_67] : k3_tarski(k2_tarski(B_66,A_67)) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_222])).

tff(c_30,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_256,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,A_67) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_30])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_242,plain,(
    ! [B_64,A_65] :
      ( r2_hidden(B_64,A_65)
      | ~ m1_subset_1(B_64,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_246,plain,(
    ! [B_64,A_17] :
      ( r1_tarski(B_64,A_17)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_242,c_18])).

tff(c_704,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_246])).

tff(c_721,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_704])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_748,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_721,c_6])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_819,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_10])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_945,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_12])).

tff(c_50,plain,(
    ! [A_35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_740,plain,(
    ! [A_95] : r1_tarski(k1_xboole_0,A_95) ),
    inference(resolution,[status(thm)],[c_50,c_704])).

tff(c_749,plain,(
    ! [A_96] : k2_xboole_0(k1_xboole_0,A_96) = A_96 ),
    inference(resolution,[status(thm)],[c_740,c_6])).

tff(c_789,plain,(
    ! [A_67] : k2_xboole_0(A_67,k1_xboole_0) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_749])).

tff(c_1181,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_789])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_722,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,B_94) = k3_subset_1(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_739,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_722])).

tff(c_808,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_12])).

tff(c_811,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_xboole_0('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_2,c_808])).

tff(c_1210,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_811])).

tff(c_1370,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_1210])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k3_subset_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1461,plain,(
    ! [A_114,B_115,C_116] :
      ( k4_subset_1(A_114,B_115,C_116) = k2_xboole_0(B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5891,plain,(
    ! [A_194,B_195,B_196] :
      ( k4_subset_1(A_194,B_195,k3_subset_1(A_194,B_196)) = k2_xboole_0(B_195,k3_subset_1(A_194,B_196))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(A_194)) ) ),
    inference(resolution,[status(thm)],[c_44,c_1461])).

tff(c_5921,plain,(
    ! [B_197] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_197)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_197))
      | ~ m1_subset_1(B_197,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_5891])).

tff(c_5948,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_5921])).

tff(c_5960,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1370,c_5948])).

tff(c_5962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_5960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/2.04  
% 4.80/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/2.04  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.80/2.04  
% 4.80/2.04  %Foreground sorts:
% 4.80/2.04  
% 4.80/2.04  
% 4.80/2.04  %Background operators:
% 4.80/2.04  
% 4.80/2.04  
% 4.80/2.04  %Foreground operators:
% 4.80/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.80/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.80/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.80/2.04  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.80/2.04  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.80/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.80/2.04  tff('#skF_3', type, '#skF_3': $i).
% 4.80/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/2.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.80/2.04  tff('#skF_4', type, '#skF_4': $i).
% 4.80/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.80/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.80/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.80/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.80/2.04  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.80/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/2.04  
% 4.80/2.06  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.80/2.06  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.80/2.06  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.80/2.06  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.80/2.06  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.80/2.06  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.80/2.06  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.80/2.06  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.80/2.06  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.80/2.06  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.80/2.06  tff(f_86, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.80/2.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.80/2.06  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.80/2.06  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.80/2.06  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.80/2.06  tff(c_40, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.80/2.06  tff(c_52, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/2.06  tff(c_55, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 4.80/2.06  tff(c_14, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.80/2.06  tff(c_222, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.80/2.06  tff(c_250, plain, (![B_66, A_67]: (k3_tarski(k2_tarski(B_66, A_67))=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_222])).
% 4.80/2.06  tff(c_30, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.80/2.06  tff(c_256, plain, (![B_66, A_67]: (k2_xboole_0(B_66, A_67)=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_250, c_30])).
% 4.80/2.06  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/2.06  tff(c_46, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.80/2.06  tff(c_242, plain, (![B_64, A_65]: (r2_hidden(B_64, A_65) | ~m1_subset_1(B_64, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.80/2.06  tff(c_18, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.80/2.06  tff(c_246, plain, (![B_64, A_17]: (r1_tarski(B_64, A_17) | ~m1_subset_1(B_64, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_242, c_18])).
% 4.80/2.06  tff(c_704, plain, (![B_91, A_92]: (r1_tarski(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)))), inference(negUnitSimplification, [status(thm)], [c_46, c_246])).
% 4.80/2.06  tff(c_721, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_704])).
% 4.80/2.06  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.80/2.06  tff(c_748, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_721, c_6])).
% 4.80/2.06  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.80/2.06  tff(c_819, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_748, c_10])).
% 4.80/2.06  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.80/2.06  tff(c_945, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_819, c_12])).
% 4.80/2.06  tff(c_50, plain, (![A_35]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.80/2.06  tff(c_740, plain, (![A_95]: (r1_tarski(k1_xboole_0, A_95))), inference(resolution, [status(thm)], [c_50, c_704])).
% 4.80/2.06  tff(c_749, plain, (![A_96]: (k2_xboole_0(k1_xboole_0, A_96)=A_96)), inference(resolution, [status(thm)], [c_740, c_6])).
% 4.80/2.06  tff(c_789, plain, (![A_67]: (k2_xboole_0(A_67, k1_xboole_0)=A_67)), inference(superposition, [status(thm), theory('equality')], [c_256, c_749])).
% 4.80/2.06  tff(c_1181, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_945, c_789])).
% 4.80/2.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.80/2.06  tff(c_722, plain, (![A_93, B_94]: (k4_xboole_0(A_93, B_94)=k3_subset_1(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.80/2.06  tff(c_739, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_722])).
% 4.80/2.06  tff(c_808, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_739, c_12])).
% 4.80/2.06  tff(c_811, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_xboole_0('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_2, c_808])).
% 4.80/2.06  tff(c_1210, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1181, c_811])).
% 4.80/2.06  tff(c_1370, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_256, c_1210])).
% 4.80/2.06  tff(c_44, plain, (![A_29, B_30]: (m1_subset_1(k3_subset_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/2.06  tff(c_1461, plain, (![A_114, B_115, C_116]: (k4_subset_1(A_114, B_115, C_116)=k2_xboole_0(B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_114)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.80/2.06  tff(c_5891, plain, (![A_194, B_195, B_196]: (k4_subset_1(A_194, B_195, k3_subset_1(A_194, B_196))=k2_xboole_0(B_195, k3_subset_1(A_194, B_196)) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)) | ~m1_subset_1(B_196, k1_zfmisc_1(A_194)))), inference(resolution, [status(thm)], [c_44, c_1461])).
% 4.80/2.06  tff(c_5921, plain, (![B_197]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_197))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_197)) | ~m1_subset_1(B_197, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_5891])).
% 4.80/2.06  tff(c_5948, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_5921])).
% 4.80/2.06  tff(c_5960, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1370, c_5948])).
% 4.80/2.06  tff(c_5962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_5960])).
% 4.80/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/2.06  
% 4.80/2.06  Inference rules
% 4.80/2.06  ----------------------
% 4.80/2.06  #Ref     : 0
% 4.80/2.06  #Sup     : 1453
% 4.80/2.06  #Fact    : 0
% 4.80/2.06  #Define  : 0
% 4.80/2.06  #Split   : 0
% 4.80/2.06  #Chain   : 0
% 4.80/2.06  #Close   : 0
% 4.80/2.06  
% 4.80/2.06  Ordering : KBO
% 4.80/2.06  
% 4.80/2.06  Simplification rules
% 4.80/2.06  ----------------------
% 4.80/2.06  #Subsume      : 36
% 4.80/2.06  #Demod        : 1568
% 4.80/2.06  #Tautology    : 1178
% 4.80/2.06  #SimpNegUnit  : 14
% 4.80/2.06  #BackRed      : 8
% 4.80/2.06  
% 4.80/2.06  #Partial instantiations: 0
% 4.80/2.06  #Strategies tried      : 1
% 4.80/2.06  
% 4.80/2.06  Timing (in seconds)
% 4.80/2.06  ----------------------
% 4.80/2.06  Preprocessing        : 0.33
% 4.80/2.06  Parsing              : 0.18
% 4.80/2.06  CNF conversion       : 0.02
% 4.80/2.06  Main loop            : 0.94
% 4.80/2.06  Inferencing          : 0.29
% 4.80/2.06  Reduction            : 0.42
% 4.80/2.06  Demodulation         : 0.35
% 4.80/2.06  BG Simplification    : 0.03
% 4.80/2.06  Subsumption          : 0.13
% 4.80/2.06  Abstraction          : 0.04
% 4.80/2.06  MUC search           : 0.00
% 4.80/2.06  Cooper               : 0.00
% 4.80/2.06  Total                : 1.29
% 4.80/2.06  Index Insertion      : 0.00
% 4.80/2.06  Index Deletion       : 0.00
% 4.80/2.06  Index Matching       : 0.00
% 4.80/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
