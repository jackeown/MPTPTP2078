%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:39 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   76 (  95 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 102 expanded)
%              Number of equality atoms :   42 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_58,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_25] : m1_subset_1(k2_subset_1(A_25),k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_41,plain,(
    ! [A_25] : m1_subset_1(A_25,k1_zfmisc_1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_495,plain,(
    ! [A_79,B_80,C_81] :
      ( k4_subset_1(A_79,B_80,C_81) = k2_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_675,plain,(
    ! [A_87,B_88] :
      ( k4_subset_1(A_87,B_88,A_87) = k2_xboole_0(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_41,c_495])).

tff(c_682,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_675])).

tff(c_38,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_38])).

tff(c_692,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_42])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(A_37,B_38)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_214,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_223,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_214])).

tff(c_229,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_223])).

tff(c_24,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_152,plain,(
    ! [B_49,A_50] : k3_tarski(k2_tarski(B_49,A_50)) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_28,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_28])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_114,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_287,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_296,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k4_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_287])).

tff(c_299,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_296])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_413,plain,(
    ! [C_74,A_75,B_76] :
      ( r2_hidden(C_74,A_75)
      | ~ r2_hidden(C_74,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1174,plain,(
    ! [A_99,B_100,A_101] :
      ( r2_hidden('#skF_1'(A_99,B_100),A_101)
      | ~ m1_subset_1(A_99,k1_zfmisc_1(A_101))
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_413])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1186,plain,(
    ! [A_102,A_103] :
      ( ~ m1_subset_1(A_102,k1_zfmisc_1(A_103))
      | r1_tarski(A_102,A_103) ) ),
    inference(resolution,[status(thm)],[c_1174,c_4])).

tff(c_1195,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1186])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1202,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1195,c_18])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1206,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1202,c_16])).

tff(c_1209,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_1206])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1214,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_22])).

tff(c_1217,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_158,c_1214])).

tff(c_1219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_1217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.51  
% 3.10/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.51  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.51  
% 3.10/1.51  %Foreground sorts:
% 3.10/1.51  
% 3.10/1.51  
% 3.10/1.51  %Background operators:
% 3.10/1.51  
% 3.10/1.51  
% 3.10/1.51  %Foreground operators:
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.10/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.51  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.10/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.10/1.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.10/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.51  
% 3.22/1.53  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.22/1.53  tff(f_58, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.22/1.53  tff(f_60, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.22/1.53  tff(f_73, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.22/1.53  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.22/1.53  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.22/1.53  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.22/1.53  tff(f_52, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.22/1.53  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.22/1.53  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.53  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.53  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.22/1.53  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.22/1.53  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.53  tff(c_30, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.53  tff(c_32, plain, (![A_25]: (m1_subset_1(k2_subset_1(A_25), k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.22/1.53  tff(c_41, plain, (![A_25]: (m1_subset_1(A_25, k1_zfmisc_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 3.22/1.53  tff(c_495, plain, (![A_79, B_80, C_81]: (k4_subset_1(A_79, B_80, C_81)=k2_xboole_0(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.53  tff(c_675, plain, (![A_87, B_88]: (k4_subset_1(A_87, B_88, A_87)=k2_xboole_0(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_41, c_495])).
% 3.22/1.53  tff(c_682, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_675])).
% 3.22/1.53  tff(c_38, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.53  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_38])).
% 3.22/1.53  tff(c_692, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_682, c_42])).
% 3.22/1.53  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.22/1.53  tff(c_64, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(A_37, B_38))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.53  tff(c_71, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 3.22/1.53  tff(c_214, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.53  tff(c_223, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_71, c_214])).
% 3.22/1.53  tff(c_229, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_223])).
% 3.22/1.53  tff(c_24, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.53  tff(c_128, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.53  tff(c_152, plain, (![B_49, A_50]: (k3_tarski(k2_tarski(B_49, A_50))=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_24, c_128])).
% 3.22/1.53  tff(c_28, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.53  tff(c_158, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_152, c_28])).
% 3.22/1.53  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.53  tff(c_114, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.53  tff(c_118, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_14, c_114])).
% 3.22/1.53  tff(c_287, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.22/1.53  tff(c_296, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k4_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_118, c_287])).
% 3.22/1.53  tff(c_299, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_296])).
% 3.22/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.53  tff(c_413, plain, (![C_74, A_75, B_76]: (r2_hidden(C_74, A_75) | ~r2_hidden(C_74, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.53  tff(c_1174, plain, (![A_99, B_100, A_101]: (r2_hidden('#skF_1'(A_99, B_100), A_101) | ~m1_subset_1(A_99, k1_zfmisc_1(A_101)) | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_6, c_413])).
% 3.22/1.53  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.53  tff(c_1186, plain, (![A_102, A_103]: (~m1_subset_1(A_102, k1_zfmisc_1(A_103)) | r1_tarski(A_102, A_103))), inference(resolution, [status(thm)], [c_1174, c_4])).
% 3.22/1.53  tff(c_1195, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_1186])).
% 3.22/1.53  tff(c_18, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.53  tff(c_1202, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1195, c_18])).
% 3.22/1.53  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.22/1.53  tff(c_1206, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1202, c_16])).
% 3.22/1.53  tff(c_1209, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_299, c_1206])).
% 3.22/1.53  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.53  tff(c_1214, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1209, c_22])).
% 3.28/1.53  tff(c_1217, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_158, c_1214])).
% 3.28/1.53  tff(c_1219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_692, c_1217])).
% 3.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  Inference rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Ref     : 0
% 3.28/1.53  #Sup     : 292
% 3.28/1.53  #Fact    : 0
% 3.28/1.53  #Define  : 0
% 3.28/1.53  #Split   : 0
% 3.28/1.53  #Chain   : 0
% 3.28/1.53  #Close   : 0
% 3.28/1.53  
% 3.28/1.53  Ordering : KBO
% 3.28/1.53  
% 3.28/1.53  Simplification rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Subsume      : 20
% 3.28/1.53  #Demod        : 345
% 3.28/1.53  #Tautology    : 230
% 3.28/1.53  #SimpNegUnit  : 1
% 3.28/1.53  #BackRed      : 1
% 3.28/1.53  
% 3.28/1.53  #Partial instantiations: 0
% 3.28/1.53  #Strategies tried      : 1
% 3.28/1.53  
% 3.28/1.53  Timing (in seconds)
% 3.28/1.53  ----------------------
% 3.28/1.53  Preprocessing        : 0.32
% 3.28/1.53  Parsing              : 0.17
% 3.28/1.53  CNF conversion       : 0.02
% 3.28/1.53  Main loop            : 0.39
% 3.28/1.53  Inferencing          : 0.13
% 3.28/1.53  Reduction            : 0.17
% 3.28/1.53  Demodulation         : 0.15
% 3.28/1.53  BG Simplification    : 0.02
% 3.28/1.53  Subsumption          : 0.05
% 3.28/1.53  Abstraction          : 0.02
% 3.28/1.53  MUC search           : 0.00
% 3.28/1.53  Cooper               : 0.00
% 3.28/1.53  Total                : 0.74
% 3.28/1.53  Index Insertion      : 0.00
% 3.28/1.53  Index Deletion       : 0.00
% 3.28/1.53  Index Matching       : 0.00
% 3.28/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
