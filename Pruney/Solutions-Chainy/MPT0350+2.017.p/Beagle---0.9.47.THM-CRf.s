%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 12.41s
% Output     : CNFRefutation 12.41s
% Verified   : 
% Statistics : Number of formulae       :   76 (  85 expanded)
%              Number of leaves         :   42 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 106 expanded)
%              Number of equality atoms :   34 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_113,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_70,plain,(
    ! [A_65] : k2_subset_1(A_65) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_83,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_80])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_76,plain,(
    ! [A_70] : ~ v1_xboole_0(k1_zfmisc_1(A_70)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_423,plain,(
    ! [B_112,A_113] :
      ( r2_hidden(B_112,A_113)
      | ~ m1_subset_1(B_112,A_113)
      | v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [C_60,A_56] :
      ( r1_tarski(C_60,A_56)
      | ~ r2_hidden(C_60,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_430,plain,(
    ! [B_112,A_56] :
      ( r1_tarski(B_112,A_56)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_56))
      | v1_xboole_0(k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_423,c_48])).

tff(c_435,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_115)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_430])).

tff(c_448,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_435])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4429,plain,(
    ! [A_234,B_235,C_236] :
      ( r1_tarski(A_234,'#skF_1'(A_234,B_235,C_236))
      | k2_xboole_0(A_234,C_236) = B_235
      | ~ r1_tarski(C_236,B_235)
      | ~ r1_tarski(A_234,B_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [B_10,A_9,C_11] :
      ( ~ r1_tarski(B_10,'#skF_1'(A_9,B_10,C_11))
      | k2_xboole_0(A_9,C_11) = B_10
      | ~ r1_tarski(C_11,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4433,plain,(
    ! [B_235,C_236] :
      ( k2_xboole_0(B_235,C_236) = B_235
      | ~ r1_tarski(C_236,B_235)
      | ~ r1_tarski(B_235,B_235) ) ),
    inference(resolution,[status(thm)],[c_4429,c_14])).

tff(c_4440,plain,(
    ! [B_237,C_238] :
      ( k2_xboole_0(B_237,C_238) = B_237
      | ~ r1_tarski(C_238,B_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4433])).

tff(c_4456,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_448,c_4440])).

tff(c_34,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_263,plain,(
    ! [A_89,B_90] : k3_tarski(k2_tarski(A_89,B_90)) = k2_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_301,plain,(
    ! [B_97,A_98] : k3_tarski(k2_tarski(B_97,A_98)) = k2_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_263])).

tff(c_60,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_307,plain,(
    ! [B_97,A_98] : k2_xboole_0(B_97,A_98) = k2_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_60])).

tff(c_1409,plain,(
    ! [A_149,B_150] :
      ( k4_xboole_0(A_149,B_150) = k3_subset_1(A_149,B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1422,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1409])).

tff(c_20,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1693,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_20])).

tff(c_1697,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_1693])).

tff(c_4461,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4456,c_1697])).

tff(c_74,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k3_subset_1(A_68,B_69),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2921,plain,(
    ! [A_196,B_197,C_198] :
      ( k4_subset_1(A_196,B_197,C_198) = k2_xboole_0(B_197,C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(A_196))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_27957,plain,(
    ! [A_429,B_430,B_431] :
      ( k4_subset_1(A_429,B_430,k3_subset_1(A_429,B_431)) = k2_xboole_0(B_430,k3_subset_1(A_429,B_431))
      | ~ m1_subset_1(B_430,k1_zfmisc_1(A_429))
      | ~ m1_subset_1(B_431,k1_zfmisc_1(A_429)) ) ),
    inference(resolution,[status(thm)],[c_74,c_2921])).

tff(c_27980,plain,(
    ! [B_432] :
      ( k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4',B_432)) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4',B_432))
      | ~ m1_subset_1(B_432,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_82,c_27957])).

tff(c_27999,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_82,c_27980])).

tff(c_28007,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4461,c_27999])).

tff(c_28009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_28007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.41/5.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.41/5.43  
% 12.41/5.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.41/5.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 12.41/5.43  
% 12.41/5.43  %Foreground sorts:
% 12.41/5.43  
% 12.41/5.43  
% 12.41/5.43  %Background operators:
% 12.41/5.43  
% 12.41/5.43  
% 12.41/5.43  %Foreground operators:
% 12.41/5.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.41/5.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.41/5.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.41/5.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.41/5.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.41/5.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.41/5.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.41/5.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.41/5.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.41/5.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.41/5.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.41/5.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.41/5.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.41/5.43  tff('#skF_5', type, '#skF_5': $i).
% 12.41/5.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.41/5.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.41/5.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.41/5.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.41/5.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.41/5.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.41/5.43  tff('#skF_4', type, '#skF_4': $i).
% 12.41/5.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.41/5.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.41/5.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.41/5.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.41/5.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.41/5.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.41/5.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.41/5.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.41/5.43  
% 12.41/5.45  tff(f_102, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.41/5.45  tff(f_124, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 12.41/5.45  tff(f_113, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.41/5.45  tff(f_100, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 12.41/5.45  tff(f_85, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.41/5.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.41/5.45  tff(f_50, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 12.41/5.45  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.41/5.45  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 12.41/5.45  tff(f_106, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.41/5.45  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.41/5.45  tff(f_110, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 12.41/5.45  tff(f_119, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.41/5.45  tff(c_70, plain, (![A_65]: (k2_subset_1(A_65)=A_65)), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.41/5.45  tff(c_80, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.41/5.45  tff(c_83, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_80])).
% 12.41/5.45  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.41/5.45  tff(c_76, plain, (![A_70]: (~v1_xboole_0(k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.41/5.45  tff(c_423, plain, (![B_112, A_113]: (r2_hidden(B_112, A_113) | ~m1_subset_1(B_112, A_113) | v1_xboole_0(A_113))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.41/5.45  tff(c_48, plain, (![C_60, A_56]: (r1_tarski(C_60, A_56) | ~r2_hidden(C_60, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.41/5.45  tff(c_430, plain, (![B_112, A_56]: (r1_tarski(B_112, A_56) | ~m1_subset_1(B_112, k1_zfmisc_1(A_56)) | v1_xboole_0(k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_423, c_48])).
% 12.41/5.45  tff(c_435, plain, (![B_114, A_115]: (r1_tarski(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(A_115)))), inference(negUnitSimplification, [status(thm)], [c_76, c_430])).
% 12.41/5.45  tff(c_448, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_435])).
% 12.41/5.45  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.41/5.45  tff(c_4429, plain, (![A_234, B_235, C_236]: (r1_tarski(A_234, '#skF_1'(A_234, B_235, C_236)) | k2_xboole_0(A_234, C_236)=B_235 | ~r1_tarski(C_236, B_235) | ~r1_tarski(A_234, B_235))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.41/5.45  tff(c_14, plain, (![B_10, A_9, C_11]: (~r1_tarski(B_10, '#skF_1'(A_9, B_10, C_11)) | k2_xboole_0(A_9, C_11)=B_10 | ~r1_tarski(C_11, B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.41/5.45  tff(c_4433, plain, (![B_235, C_236]: (k2_xboole_0(B_235, C_236)=B_235 | ~r1_tarski(C_236, B_235) | ~r1_tarski(B_235, B_235))), inference(resolution, [status(thm)], [c_4429, c_14])).
% 12.41/5.45  tff(c_4440, plain, (![B_237, C_238]: (k2_xboole_0(B_237, C_238)=B_237 | ~r1_tarski(C_238, B_237))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4433])).
% 12.41/5.45  tff(c_4456, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_448, c_4440])).
% 12.41/5.45  tff(c_34, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.41/5.45  tff(c_263, plain, (![A_89, B_90]: (k3_tarski(k2_tarski(A_89, B_90))=k2_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.41/5.45  tff(c_301, plain, (![B_97, A_98]: (k3_tarski(k2_tarski(B_97, A_98))=k2_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_34, c_263])).
% 12.41/5.45  tff(c_60, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.41/5.45  tff(c_307, plain, (![B_97, A_98]: (k2_xboole_0(B_97, A_98)=k2_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_301, c_60])).
% 12.41/5.45  tff(c_1409, plain, (![A_149, B_150]: (k4_xboole_0(A_149, B_150)=k3_subset_1(A_149, B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.41/5.45  tff(c_1422, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_1409])).
% 12.41/5.45  tff(c_20, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.41/5.45  tff(c_1693, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1422, c_20])).
% 12.41/5.45  tff(c_1697, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_1693])).
% 12.41/5.45  tff(c_4461, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4456, c_1697])).
% 12.41/5.45  tff(c_74, plain, (![A_68, B_69]: (m1_subset_1(k3_subset_1(A_68, B_69), k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.41/5.45  tff(c_2921, plain, (![A_196, B_197, C_198]: (k4_subset_1(A_196, B_197, C_198)=k2_xboole_0(B_197, C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(A_196)) | ~m1_subset_1(B_197, k1_zfmisc_1(A_196)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.41/5.45  tff(c_27957, plain, (![A_429, B_430, B_431]: (k4_subset_1(A_429, B_430, k3_subset_1(A_429, B_431))=k2_xboole_0(B_430, k3_subset_1(A_429, B_431)) | ~m1_subset_1(B_430, k1_zfmisc_1(A_429)) | ~m1_subset_1(B_431, k1_zfmisc_1(A_429)))), inference(resolution, [status(thm)], [c_74, c_2921])).
% 12.41/5.45  tff(c_27980, plain, (![B_432]: (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', B_432))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', B_432)) | ~m1_subset_1(B_432, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_82, c_27957])).
% 12.41/5.45  tff(c_27999, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_27980])).
% 12.41/5.45  tff(c_28007, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4461, c_27999])).
% 12.41/5.45  tff(c_28009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_28007])).
% 12.41/5.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.41/5.45  
% 12.41/5.45  Inference rules
% 12.41/5.45  ----------------------
% 12.41/5.45  #Ref     : 0
% 12.41/5.45  #Sup     : 6937
% 12.41/5.45  #Fact    : 0
% 12.41/5.45  #Define  : 0
% 12.41/5.45  #Split   : 1
% 12.41/5.45  #Chain   : 0
% 12.41/5.45  #Close   : 0
% 12.41/5.45  
% 12.41/5.45  Ordering : KBO
% 12.41/5.45  
% 12.41/5.45  Simplification rules
% 12.41/5.45  ----------------------
% 12.41/5.45  #Subsume      : 211
% 12.41/5.45  #Demod        : 10562
% 12.41/5.45  #Tautology    : 4225
% 12.41/5.45  #SimpNegUnit  : 14
% 12.41/5.45  #BackRed      : 14
% 12.41/5.45  
% 12.41/5.45  #Partial instantiations: 0
% 12.41/5.45  #Strategies tried      : 1
% 12.41/5.45  
% 12.41/5.45  Timing (in seconds)
% 12.41/5.45  ----------------------
% 12.41/5.45  Preprocessing        : 0.34
% 12.41/5.45  Parsing              : 0.17
% 12.41/5.45  CNF conversion       : 0.02
% 12.41/5.45  Main loop            : 4.36
% 12.41/5.45  Inferencing          : 0.70
% 12.41/5.45  Reduction            : 2.76
% 12.41/5.45  Demodulation         : 2.50
% 12.41/5.45  BG Simplification    : 0.10
% 12.41/5.45  Subsumption          : 0.62
% 12.41/5.45  Abstraction          : 0.16
% 12.41/5.45  MUC search           : 0.00
% 12.41/5.45  Cooper               : 0.00
% 12.41/5.45  Total                : 4.73
% 12.41/5.45  Index Insertion      : 0.00
% 12.41/5.45  Index Deletion       : 0.00
% 12.41/5.45  Index Matching       : 0.00
% 12.41/5.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
