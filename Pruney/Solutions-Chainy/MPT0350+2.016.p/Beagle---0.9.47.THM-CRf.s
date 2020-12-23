%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 17.78s
% Output     : CNFRefutation 17.78s
% Verified   : 
% Statistics : Number of formulae       :   77 (  94 expanded)
%              Number of leaves         :   42 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 115 expanded)
%              Number of equality atoms :   35 (  49 expanded)
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

tff(f_98,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_109,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_66,plain,(
    ! [A_61] : k2_subset_1(A_61) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_76,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_79,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_76])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_72,plain,(
    ! [A_66] : ~ v1_xboole_0(k1_zfmisc_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_403,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(B_103,A_104)
      | ~ m1_subset_1(B_103,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [C_56,A_52] :
      ( r1_tarski(C_56,A_52)
      | ~ r2_hidden(C_56,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_407,plain,(
    ! [B_103,A_52] :
      ( r1_tarski(B_103,A_52)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_52))
      | v1_xboole_0(k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_403,c_44])).

tff(c_445,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_109)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_407])).

tff(c_454,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_445])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2779,plain,(
    ! [C_207,A_208,B_209] :
      ( r1_tarski(C_207,'#skF_1'(A_208,B_209,C_207))
      | k2_xboole_0(A_208,C_207) = B_209
      | ~ r1_tarski(C_207,B_209)
      | ~ r1_tarski(A_208,B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [B_12,A_11,C_13] :
      ( ~ r1_tarski(B_12,'#skF_1'(A_11,B_12,C_13))
      | k2_xboole_0(A_11,C_13) = B_12
      | ~ r1_tarski(C_13,B_12)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2783,plain,(
    ! [A_208,B_209] :
      ( k2_xboole_0(A_208,B_209) = B_209
      | ~ r1_tarski(B_209,B_209)
      | ~ r1_tarski(A_208,B_209) ) ),
    inference(resolution,[status(thm)],[c_2779,c_16])).

tff(c_2794,plain,(
    ! [A_210,B_211] :
      ( k2_xboole_0(A_210,B_211) = B_211
      | ~ r1_tarski(A_210,B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2783])).

tff(c_2820,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_454,c_2794])).

tff(c_30,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_199,plain,(
    ! [A_88,B_89] : k3_tarski(k2_tarski(A_88,B_89)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_223,plain,(
    ! [A_92,B_93] : k3_tarski(k2_tarski(A_92,B_93)) = k2_xboole_0(B_93,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_199])).

tff(c_56,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_229,plain,(
    ! [B_93,A_92] : k2_xboole_0(B_93,A_92) = k2_xboole_0(A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_56])).

tff(c_2829,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2820,c_229])).

tff(c_729,plain,(
    ! [A_128,B_129] :
      ( k4_xboole_0(A_128,B_129) = k3_subset_1(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_746,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_729])).

tff(c_22,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_750,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_22])).

tff(c_753,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_750])).

tff(c_2864,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2829,c_753])).

tff(c_70,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k3_subset_1(A_64,B_65),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2337,plain,(
    ! [A_176,B_177,C_178] :
      ( k4_subset_1(A_176,B_177,C_178) = k2_xboole_0(B_177,C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(A_176))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38260,plain,(
    ! [A_415,B_416,B_417] :
      ( k4_subset_1(A_415,B_416,k3_subset_1(A_415,B_417)) = k2_xboole_0(B_416,k3_subset_1(A_415,B_417))
      | ~ m1_subset_1(B_416,k1_zfmisc_1(A_415))
      | ~ m1_subset_1(B_417,k1_zfmisc_1(A_415)) ) ),
    inference(resolution,[status(thm)],[c_70,c_2337])).

tff(c_39723,plain,(
    ! [B_421] :
      ( k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4',B_421)) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4',B_421))
      | ~ m1_subset_1(B_421,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_78,c_38260])).

tff(c_39750,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_78,c_39723])).

tff(c_39762,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2864,c_39750])).

tff(c_39764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_39762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:36:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.78/10.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.78/10.65  
% 17.78/10.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.78/10.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 17.78/10.66  
% 17.78/10.66  %Foreground sorts:
% 17.78/10.66  
% 17.78/10.66  
% 17.78/10.66  %Background operators:
% 17.78/10.66  
% 17.78/10.66  
% 17.78/10.66  %Foreground operators:
% 17.78/10.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.78/10.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.78/10.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.78/10.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.78/10.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.78/10.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.78/10.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.78/10.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.78/10.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.78/10.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.78/10.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.78/10.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.78/10.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 17.78/10.66  tff('#skF_5', type, '#skF_5': $i).
% 17.78/10.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.78/10.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.78/10.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.78/10.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.78/10.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.78/10.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.78/10.66  tff('#skF_4', type, '#skF_4': $i).
% 17.78/10.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.78/10.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.78/10.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.78/10.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.78/10.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.78/10.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 17.78/10.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.78/10.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.78/10.66  
% 17.78/10.67  tff(f_98, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 17.78/10.67  tff(f_120, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 17.78/10.67  tff(f_109, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 17.78/10.67  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 17.78/10.67  tff(f_81, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 17.78/10.67  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.78/10.67  tff(f_52, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 17.78/10.67  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 17.78/10.67  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.78/10.67  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 17.78/10.67  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 17.78/10.67  tff(f_106, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 17.78/10.67  tff(f_115, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 17.78/10.67  tff(c_66, plain, (![A_61]: (k2_subset_1(A_61)=A_61)), inference(cnfTransformation, [status(thm)], [f_98])).
% 17.78/10.67  tff(c_76, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.78/10.67  tff(c_79, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_76])).
% 17.78/10.67  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.78/10.67  tff(c_72, plain, (![A_66]: (~v1_xboole_0(k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 17.78/10.67  tff(c_403, plain, (![B_103, A_104]: (r2_hidden(B_103, A_104) | ~m1_subset_1(B_103, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_96])).
% 17.78/10.67  tff(c_44, plain, (![C_56, A_52]: (r1_tarski(C_56, A_52) | ~r2_hidden(C_56, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.78/10.67  tff(c_407, plain, (![B_103, A_52]: (r1_tarski(B_103, A_52) | ~m1_subset_1(B_103, k1_zfmisc_1(A_52)) | v1_xboole_0(k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_403, c_44])).
% 17.78/10.67  tff(c_445, plain, (![B_108, A_109]: (r1_tarski(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(A_109)))), inference(negUnitSimplification, [status(thm)], [c_72, c_407])).
% 17.78/10.67  tff(c_454, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_445])).
% 17.78/10.67  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.78/10.67  tff(c_2779, plain, (![C_207, A_208, B_209]: (r1_tarski(C_207, '#skF_1'(A_208, B_209, C_207)) | k2_xboole_0(A_208, C_207)=B_209 | ~r1_tarski(C_207, B_209) | ~r1_tarski(A_208, B_209))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.78/10.67  tff(c_16, plain, (![B_12, A_11, C_13]: (~r1_tarski(B_12, '#skF_1'(A_11, B_12, C_13)) | k2_xboole_0(A_11, C_13)=B_12 | ~r1_tarski(C_13, B_12) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.78/10.67  tff(c_2783, plain, (![A_208, B_209]: (k2_xboole_0(A_208, B_209)=B_209 | ~r1_tarski(B_209, B_209) | ~r1_tarski(A_208, B_209))), inference(resolution, [status(thm)], [c_2779, c_16])).
% 17.78/10.67  tff(c_2794, plain, (![A_210, B_211]: (k2_xboole_0(A_210, B_211)=B_211 | ~r1_tarski(A_210, B_211))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2783])).
% 17.78/10.67  tff(c_2820, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_454, c_2794])).
% 17.78/10.67  tff(c_30, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.78/10.67  tff(c_199, plain, (![A_88, B_89]: (k3_tarski(k2_tarski(A_88, B_89))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.78/10.67  tff(c_223, plain, (![A_92, B_93]: (k3_tarski(k2_tarski(A_92, B_93))=k2_xboole_0(B_93, A_92))), inference(superposition, [status(thm), theory('equality')], [c_30, c_199])).
% 17.78/10.67  tff(c_56, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.78/10.67  tff(c_229, plain, (![B_93, A_92]: (k2_xboole_0(B_93, A_92)=k2_xboole_0(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_223, c_56])).
% 17.78/10.67  tff(c_2829, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2820, c_229])).
% 17.78/10.67  tff(c_729, plain, (![A_128, B_129]: (k4_xboole_0(A_128, B_129)=k3_subset_1(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 17.78/10.67  tff(c_746, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_729])).
% 17.78/10.67  tff(c_22, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.78/10.67  tff(c_750, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_746, c_22])).
% 17.78/10.67  tff(c_753, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_750])).
% 17.78/10.67  tff(c_2864, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2829, c_753])).
% 17.78/10.67  tff(c_70, plain, (![A_64, B_65]: (m1_subset_1(k3_subset_1(A_64, B_65), k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.78/10.67  tff(c_2337, plain, (![A_176, B_177, C_178]: (k4_subset_1(A_176, B_177, C_178)=k2_xboole_0(B_177, C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(A_176)) | ~m1_subset_1(B_177, k1_zfmisc_1(A_176)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.78/10.67  tff(c_38260, plain, (![A_415, B_416, B_417]: (k4_subset_1(A_415, B_416, k3_subset_1(A_415, B_417))=k2_xboole_0(B_416, k3_subset_1(A_415, B_417)) | ~m1_subset_1(B_416, k1_zfmisc_1(A_415)) | ~m1_subset_1(B_417, k1_zfmisc_1(A_415)))), inference(resolution, [status(thm)], [c_70, c_2337])).
% 17.78/10.67  tff(c_39723, plain, (![B_421]: (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', B_421))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', B_421)) | ~m1_subset_1(B_421, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_78, c_38260])).
% 17.78/10.67  tff(c_39750, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_78, c_39723])).
% 17.78/10.67  tff(c_39762, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2864, c_39750])).
% 17.78/10.67  tff(c_39764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_39762])).
% 17.78/10.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.78/10.67  
% 17.78/10.67  Inference rules
% 17.78/10.67  ----------------------
% 17.78/10.67  #Ref     : 0
% 17.78/10.67  #Sup     : 10356
% 17.78/10.67  #Fact    : 0
% 17.78/10.67  #Define  : 0
% 17.78/10.67  #Split   : 1
% 17.78/10.67  #Chain   : 0
% 17.78/10.67  #Close   : 0
% 17.78/10.67  
% 17.78/10.67  Ordering : KBO
% 17.78/10.67  
% 17.78/10.67  Simplification rules
% 17.78/10.67  ----------------------
% 17.78/10.67  #Subsume      : 665
% 17.78/10.67  #Demod        : 14527
% 17.78/10.67  #Tautology    : 3876
% 17.78/10.67  #SimpNegUnit  : 16
% 17.78/10.67  #BackRed      : 18
% 17.78/10.67  
% 17.78/10.67  #Partial instantiations: 0
% 17.78/10.67  #Strategies tried      : 1
% 17.78/10.67  
% 17.78/10.67  Timing (in seconds)
% 17.78/10.67  ----------------------
% 17.78/10.67  Preprocessing        : 0.35
% 17.78/10.67  Parsing              : 0.18
% 17.78/10.67  CNF conversion       : 0.03
% 17.78/10.67  Main loop            : 9.57
% 17.78/10.67  Inferencing          : 1.06
% 17.78/10.67  Reduction            : 7.00
% 17.78/10.67  Demodulation         : 6.63
% 17.78/10.67  BG Simplification    : 0.18
% 17.78/10.67  Subsumption          : 1.10
% 17.78/10.67  Abstraction          : 0.28
% 17.78/10.67  MUC search           : 0.00
% 17.78/10.67  Cooper               : 0.00
% 17.78/10.67  Total                : 9.95
% 17.78/10.67  Index Insertion      : 0.00
% 17.78/10.67  Index Deletion       : 0.00
% 17.78/10.67  Index Matching       : 0.00
% 17.78/10.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
