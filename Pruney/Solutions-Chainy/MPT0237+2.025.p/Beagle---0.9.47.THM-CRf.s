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
% DateTime   : Thu Dec  3 09:49:48 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 185 expanded)
%              Number of leaves         :   37 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 220 expanded)
%              Number of equality atoms :   54 ( 137 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_177,plain,(
    ! [A_79,B_80] :
      ( ~ r1_xboole_0(A_79,B_80)
      | k3_xboole_0(A_79,B_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_217,plain,(
    ! [A_84,B_85] : k3_xboole_0(k4_xboole_0(A_84,B_85),B_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_177])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_228,plain,(
    ! [B_85,A_84] : k3_xboole_0(B_85,k4_xboole_0(A_84,B_85)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_2])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_282,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_310,plain,(
    ! [A_96,B_97] : r1_xboole_0(k3_xboole_0(A_96,B_97),k4_xboole_0(A_96,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_16])).

tff(c_337,plain,(
    ! [A_98] : r1_xboole_0(A_98,k4_xboole_0(A_98,A_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_310])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_356,plain,(
    ! [A_102] : k4_xboole_0(A_102,k4_xboole_0(A_102,A_102)) = A_102 ),
    inference(resolution,[status(thm)],[c_337,c_18])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_365,plain,(
    ! [A_102] : k3_xboole_0(A_102,k4_xboole_0(A_102,A_102)) = k4_xboole_0(A_102,A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_14])).

tff(c_390,plain,(
    ! [A_102] : k4_xboole_0(A_102,A_102) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_365])).

tff(c_346,plain,(
    ! [A_98] : k4_xboole_0(A_98,k4_xboole_0(A_98,A_98)) = A_98 ),
    inference(resolution,[status(thm)],[c_337,c_18])).

tff(c_410,plain,(
    ! [A_98] : k4_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_346])).

tff(c_480,plain,(
    ! [A_108] : k4_xboole_0(A_108,k1_xboole_0) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_346])).

tff(c_189,plain,(
    ! [A_16,B_17] : k3_xboole_0(k4_xboole_0(A_16,B_17),B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_177])).

tff(c_605,plain,(
    ! [A_113] : k3_xboole_0(A_113,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_189])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_622,plain,(
    ! [A_113] : k5_xboole_0(A_113,k1_xboole_0) = k4_xboole_0(A_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_12])).

tff(c_662,plain,(
    ! [A_113] : k5_xboole_0(A_113,k1_xboole_0) = A_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_622])).

tff(c_415,plain,(
    ! [A_104] : k4_xboole_0(A_104,A_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_365])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_429,plain,(
    ! [A_104] : k5_xboole_0(A_104,k1_xboole_0) = k2_xboole_0(A_104,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_22])).

tff(c_911,plain,(
    ! [A_104] : k2_xboole_0(A_104,A_104) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_429])).

tff(c_24,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_54,B_55] :
      ( k5_xboole_0(k1_tarski(A_54),k1_tarski(B_55)) = k2_tarski(A_54,B_55)
      | B_55 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),k1_tarski(B_53))
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = A_65
      | ~ r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1944,plain,(
    ! [A_185,B_186] :
      ( k4_xboole_0(k1_tarski(A_185),k1_tarski(B_186)) = k1_tarski(A_185)
      | B_186 = A_185 ) ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_5985,plain,(
    ! [B_255,A_256] :
      ( k5_xboole_0(k1_tarski(B_255),k1_tarski(A_256)) = k2_xboole_0(k1_tarski(B_255),k1_tarski(A_256))
      | B_255 = A_256 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1944,c_22])).

tff(c_18036,plain,(
    ! [A_354,B_355] :
      ( k2_xboole_0(k1_tarski(A_354),k1_tarski(B_355)) = k2_tarski(A_354,B_355)
      | B_355 = A_354
      | B_355 = A_354 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5985])).

tff(c_38,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_45,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_44])).

tff(c_18057,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18036,c_45])).

tff(c_18061,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18057,c_18057,c_45])).

tff(c_18064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_24,c_18061])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:06:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.55/3.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.55/3.38  
% 8.55/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.55/3.38  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.55/3.38  
% 8.55/3.38  %Foreground sorts:
% 8.55/3.38  
% 8.55/3.38  
% 8.55/3.38  %Background operators:
% 8.55/3.38  
% 8.55/3.38  
% 8.55/3.38  %Foreground operators:
% 8.55/3.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.55/3.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.55/3.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.55/3.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.55/3.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.55/3.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.55/3.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.55/3.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.55/3.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.55/3.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.55/3.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.55/3.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.55/3.38  tff('#skF_3', type, '#skF_3': $i).
% 8.55/3.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.55/3.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.55/3.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.55/3.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.55/3.38  tff('#skF_4', type, '#skF_4': $i).
% 8.55/3.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.55/3.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.55/3.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.55/3.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.55/3.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.55/3.38  
% 8.55/3.40  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.55/3.40  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.55/3.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.55/3.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.55/3.40  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.55/3.40  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.55/3.40  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.55/3.40  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.55/3.40  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.55/3.40  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.55/3.40  tff(f_89, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 8.55/3.40  tff(f_84, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 8.55/3.40  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.55/3.40  tff(f_92, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 8.55/3.40  tff(c_16, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.55/3.40  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.55/3.40  tff(c_152, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.55/3.40  tff(c_177, plain, (![A_79, B_80]: (~r1_xboole_0(A_79, B_80) | k3_xboole_0(A_79, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_152])).
% 8.55/3.40  tff(c_217, plain, (![A_84, B_85]: (k3_xboole_0(k4_xboole_0(A_84, B_85), B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_177])).
% 8.55/3.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.55/3.40  tff(c_228, plain, (![B_85, A_84]: (k3_xboole_0(B_85, k4_xboole_0(A_84, B_85))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_217, c_2])).
% 8.55/3.40  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.55/3.40  tff(c_282, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.55/3.40  tff(c_310, plain, (![A_96, B_97]: (r1_xboole_0(k3_xboole_0(A_96, B_97), k4_xboole_0(A_96, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_16])).
% 8.55/3.40  tff(c_337, plain, (![A_98]: (r1_xboole_0(A_98, k4_xboole_0(A_98, A_98)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_310])).
% 8.55/3.40  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.55/3.40  tff(c_356, plain, (![A_102]: (k4_xboole_0(A_102, k4_xboole_0(A_102, A_102))=A_102)), inference(resolution, [status(thm)], [c_337, c_18])).
% 8.55/3.40  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.55/3.40  tff(c_365, plain, (![A_102]: (k3_xboole_0(A_102, k4_xboole_0(A_102, A_102))=k4_xboole_0(A_102, A_102))), inference(superposition, [status(thm), theory('equality')], [c_356, c_14])).
% 8.55/3.40  tff(c_390, plain, (![A_102]: (k4_xboole_0(A_102, A_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_365])).
% 8.55/3.40  tff(c_346, plain, (![A_98]: (k4_xboole_0(A_98, k4_xboole_0(A_98, A_98))=A_98)), inference(resolution, [status(thm)], [c_337, c_18])).
% 8.55/3.40  tff(c_410, plain, (![A_98]: (k4_xboole_0(A_98, k1_xboole_0)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_390, c_346])).
% 8.55/3.40  tff(c_480, plain, (![A_108]: (k4_xboole_0(A_108, k1_xboole_0)=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_390, c_346])).
% 8.55/3.40  tff(c_189, plain, (![A_16, B_17]: (k3_xboole_0(k4_xboole_0(A_16, B_17), B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_177])).
% 8.55/3.40  tff(c_605, plain, (![A_113]: (k3_xboole_0(A_113, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_480, c_189])).
% 8.55/3.40  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.55/3.40  tff(c_622, plain, (![A_113]: (k5_xboole_0(A_113, k1_xboole_0)=k4_xboole_0(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_605, c_12])).
% 8.55/3.40  tff(c_662, plain, (![A_113]: (k5_xboole_0(A_113, k1_xboole_0)=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_410, c_622])).
% 8.55/3.40  tff(c_415, plain, (![A_104]: (k4_xboole_0(A_104, A_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_365])).
% 8.55/3.40  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/3.40  tff(c_429, plain, (![A_104]: (k5_xboole_0(A_104, k1_xboole_0)=k2_xboole_0(A_104, A_104))), inference(superposition, [status(thm), theory('equality')], [c_415, c_22])).
% 8.55/3.40  tff(c_911, plain, (![A_104]: (k2_xboole_0(A_104, A_104)=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_662, c_429])).
% 8.55/3.40  tff(c_24, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.55/3.40  tff(c_42, plain, (![A_54, B_55]: (k5_xboole_0(k1_tarski(A_54), k1_tarski(B_55))=k2_tarski(A_54, B_55) | B_55=A_54)), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.55/3.40  tff(c_40, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), k1_tarski(B_53)) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.55/3.40  tff(c_100, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=A_65 | ~r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.55/3.40  tff(c_1944, plain, (![A_185, B_186]: (k4_xboole_0(k1_tarski(A_185), k1_tarski(B_186))=k1_tarski(A_185) | B_186=A_185)), inference(resolution, [status(thm)], [c_40, c_100])).
% 8.55/3.40  tff(c_5985, plain, (![B_255, A_256]: (k5_xboole_0(k1_tarski(B_255), k1_tarski(A_256))=k2_xboole_0(k1_tarski(B_255), k1_tarski(A_256)) | B_255=A_256)), inference(superposition, [status(thm), theory('equality')], [c_1944, c_22])).
% 8.55/3.40  tff(c_18036, plain, (![A_354, B_355]: (k2_xboole_0(k1_tarski(A_354), k1_tarski(B_355))=k2_tarski(A_354, B_355) | B_355=A_354 | B_355=A_354)), inference(superposition, [status(thm), theory('equality')], [c_42, c_5985])).
% 8.55/3.40  tff(c_38, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.55/3.40  tff(c_44, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.55/3.40  tff(c_45, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_44])).
% 8.55/3.40  tff(c_18057, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18036, c_45])).
% 8.55/3.40  tff(c_18061, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18057, c_18057, c_45])).
% 8.55/3.40  tff(c_18064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_911, c_24, c_18061])).
% 8.55/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.55/3.40  
% 8.55/3.40  Inference rules
% 8.55/3.40  ----------------------
% 8.55/3.40  #Ref     : 0
% 8.55/3.40  #Sup     : 4400
% 8.55/3.40  #Fact    : 0
% 8.55/3.40  #Define  : 0
% 8.55/3.40  #Split   : 0
% 8.55/3.40  #Chain   : 0
% 8.55/3.40  #Close   : 0
% 8.55/3.40  
% 8.55/3.40  Ordering : KBO
% 8.55/3.40  
% 8.55/3.40  Simplification rules
% 8.55/3.40  ----------------------
% 8.55/3.40  #Subsume      : 566
% 8.55/3.40  #Demod        : 6985
% 8.55/3.40  #Tautology    : 2892
% 8.55/3.40  #SimpNegUnit  : 38
% 8.55/3.40  #BackRed      : 6
% 8.55/3.40  
% 8.55/3.40  #Partial instantiations: 0
% 8.55/3.40  #Strategies tried      : 1
% 8.55/3.40  
% 8.55/3.40  Timing (in seconds)
% 8.55/3.40  ----------------------
% 8.55/3.40  Preprocessing        : 0.32
% 8.55/3.40  Parsing              : 0.17
% 8.55/3.40  CNF conversion       : 0.02
% 8.55/3.40  Main loop            : 2.33
% 8.55/3.40  Inferencing          : 0.51
% 8.55/3.40  Reduction            : 1.31
% 8.55/3.40  Demodulation         : 1.16
% 8.55/3.40  BG Simplification    : 0.06
% 8.55/3.40  Subsumption          : 0.34
% 8.55/3.40  Abstraction          : 0.12
% 8.55/3.40  MUC search           : 0.00
% 8.55/3.40  Cooper               : 0.00
% 8.55/3.40  Total                : 2.68
% 8.55/3.40  Index Insertion      : 0.00
% 8.55/3.40  Index Deletion       : 0.00
% 8.55/3.40  Index Matching       : 0.00
% 8.55/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
