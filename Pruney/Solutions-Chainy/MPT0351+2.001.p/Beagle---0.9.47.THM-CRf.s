%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 128 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 150 expanded)
%              Number of equality atoms :   49 (  81 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_60,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_26] : m1_subset_1(k2_subset_1(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    ! [A_26] : m1_subset_1(A_26,k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_710,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_subset_1(A_86,B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1128,plain,(
    ! [A_105,B_106] :
      ( k4_subset_1(A_105,B_106,A_105) = k2_xboole_0(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_46,c_710])).

tff(c_1138,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1128])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_45,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_42])).

tff(c_1168,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_45])).

tff(c_26,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_158,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_173,plain,(
    ! [B_51,A_52] : k3_tarski(k2_tarski(B_51,A_52)) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_158])).

tff(c_30,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_179,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    ! [A_34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_556,plain,(
    ! [C_80,A_81,B_82] :
      ( r2_hidden(C_80,A_81)
      | ~ r2_hidden(C_80,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1211,plain,(
    ! [A_109,B_110,A_111] :
      ( r2_hidden('#skF_1'(A_109,B_110),A_111)
      | ~ m1_subset_1(A_109,k1_zfmisc_1(A_111))
      | r1_tarski(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_8,c_556])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1223,plain,(
    ! [A_112,A_113] :
      ( ~ m1_subset_1(A_112,k1_zfmisc_1(A_113))
      | r1_tarski(A_112,A_113) ) ),
    inference(resolution,[status(thm)],[c_1211,c_6])).

tff(c_1237,plain,(
    ! [A_114] : r1_tarski(k1_xboole_0,A_114) ),
    inference(resolution,[status(thm)],[c_40,c_1223])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1327,plain,(
    ! [A_117] : k3_xboole_0(k1_xboole_0,A_117) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1237,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1371,plain,(
    ! [A_117] : k3_xboole_0(A_117,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1327,c_2])).

tff(c_196,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_212,plain,(
    ! [A_54] : k2_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_18])).

tff(c_327,plain,(
    ! [A_63,B_64] : k2_xboole_0(A_63,k4_xboole_0(B_64,A_63)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_334,plain,(
    ! [B_64] : k4_xboole_0(B_64,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_212])).

tff(c_350,plain,(
    ! [B_65] : k4_xboole_0(B_65,k1_xboole_0) = B_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_334])).

tff(c_24,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_359,plain,(
    ! [B_65] : k4_xboole_0(B_65,B_65) = k3_xboole_0(B_65,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_24])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_144,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_243,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_252,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k4_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_243])).

tff(c_367,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k3_xboole_0(B_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_252])).

tff(c_1236,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1223])).

tff(c_1251,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1236,c_20])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1416,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1251,c_16])).

tff(c_1420,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k3_xboole_0('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_1416])).

tff(c_1804,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1420])).

tff(c_22,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1814,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1804,c_22])).

tff(c_1822,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_18,c_1814])).

tff(c_1824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1168,c_1822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.63  
% 3.44/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.63  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.44/1.63  
% 3.44/1.63  %Foreground sorts:
% 3.44/1.63  
% 3.44/1.63  
% 3.44/1.63  %Background operators:
% 3.44/1.63  
% 3.44/1.63  
% 3.44/1.63  %Foreground operators:
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.63  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.44/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.44/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.63  
% 3.44/1.64  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.44/1.64  tff(f_60, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.44/1.64  tff(f_62, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.44/1.64  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.44/1.64  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.44/1.64  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.44/1.64  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.44/1.64  tff(f_77, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.44/1.64  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.44/1.64  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.44/1.64  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.44/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.44/1.64  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.44/1.64  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.44/1.64  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.64  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.44/1.64  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.44/1.64  tff(c_32, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.44/1.64  tff(c_34, plain, (![A_26]: (m1_subset_1(k2_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.64  tff(c_46, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.44/1.64  tff(c_710, plain, (![A_86, B_87, C_88]: (k4_subset_1(A_86, B_87, C_88)=k2_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.44/1.64  tff(c_1128, plain, (![A_105, B_106]: (k4_subset_1(A_105, B_106, A_105)=k2_xboole_0(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_46, c_710])).
% 3.44/1.64  tff(c_1138, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_1128])).
% 3.44/1.64  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.44/1.64  tff(c_45, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_42])).
% 3.44/1.64  tff(c_1168, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_45])).
% 3.44/1.64  tff(c_26, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.64  tff(c_158, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.64  tff(c_173, plain, (![B_51, A_52]: (k3_tarski(k2_tarski(B_51, A_52))=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_26, c_158])).
% 3.44/1.64  tff(c_30, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.64  tff(c_179, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_173, c_30])).
% 3.44/1.64  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.64  tff(c_40, plain, (![A_34]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.64  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.64  tff(c_556, plain, (![C_80, A_81, B_82]: (r2_hidden(C_80, A_81) | ~r2_hidden(C_80, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.64  tff(c_1211, plain, (![A_109, B_110, A_111]: (r2_hidden('#skF_1'(A_109, B_110), A_111) | ~m1_subset_1(A_109, k1_zfmisc_1(A_111)) | r1_tarski(A_109, B_110))), inference(resolution, [status(thm)], [c_8, c_556])).
% 3.44/1.64  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.64  tff(c_1223, plain, (![A_112, A_113]: (~m1_subset_1(A_112, k1_zfmisc_1(A_113)) | r1_tarski(A_112, A_113))), inference(resolution, [status(thm)], [c_1211, c_6])).
% 3.44/1.64  tff(c_1237, plain, (![A_114]: (r1_tarski(k1_xboole_0, A_114))), inference(resolution, [status(thm)], [c_40, c_1223])).
% 3.44/1.64  tff(c_20, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.44/1.64  tff(c_1327, plain, (![A_117]: (k3_xboole_0(k1_xboole_0, A_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1237, c_20])).
% 3.44/1.64  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.64  tff(c_1371, plain, (![A_117]: (k3_xboole_0(A_117, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1327, c_2])).
% 3.44/1.64  tff(c_196, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_173, c_30])).
% 3.44/1.64  tff(c_212, plain, (![A_54]: (k2_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_196, c_18])).
% 3.44/1.64  tff(c_327, plain, (![A_63, B_64]: (k2_xboole_0(A_63, k4_xboole_0(B_64, A_63))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.64  tff(c_334, plain, (![B_64]: (k4_xboole_0(B_64, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_64))), inference(superposition, [status(thm), theory('equality')], [c_327, c_212])).
% 3.44/1.64  tff(c_350, plain, (![B_65]: (k4_xboole_0(B_65, k1_xboole_0)=B_65)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_334])).
% 3.44/1.64  tff(c_24, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.44/1.64  tff(c_359, plain, (![B_65]: (k4_xboole_0(B_65, B_65)=k3_xboole_0(B_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_350, c_24])).
% 3.44/1.64  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.44/1.64  tff(c_144, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.44/1.64  tff(c_148, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_14, c_144])).
% 3.44/1.64  tff(c_243, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.64  tff(c_252, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k4_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_148, c_243])).
% 3.44/1.64  tff(c_367, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k3_xboole_0(B_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_252])).
% 3.44/1.64  tff(c_1236, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_1223])).
% 3.44/1.64  tff(c_1251, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1236, c_20])).
% 3.44/1.64  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.64  tff(c_1416, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1251, c_16])).
% 3.44/1.64  tff(c_1420, plain, (k4_xboole_0('#skF_3', '#skF_2')=k3_xboole_0('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_367, c_1416])).
% 3.44/1.64  tff(c_1804, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1420])).
% 3.44/1.64  tff(c_22, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.64  tff(c_1814, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1804, c_22])).
% 3.44/1.64  tff(c_1822, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_18, c_1814])).
% 3.44/1.64  tff(c_1824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1168, c_1822])).
% 3.44/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.64  
% 3.44/1.64  Inference rules
% 3.44/1.64  ----------------------
% 3.44/1.64  #Ref     : 0
% 3.44/1.64  #Sup     : 409
% 3.44/1.64  #Fact    : 0
% 3.44/1.64  #Define  : 0
% 3.44/1.64  #Split   : 1
% 3.44/1.64  #Chain   : 0
% 3.44/1.64  #Close   : 0
% 3.44/1.64  
% 3.44/1.64  Ordering : KBO
% 3.44/1.64  
% 3.44/1.64  Simplification rules
% 3.44/1.64  ----------------------
% 3.44/1.64  #Subsume      : 14
% 3.44/1.64  #Demod        : 386
% 3.44/1.64  #Tautology    : 319
% 3.44/1.64  #SimpNegUnit  : 1
% 3.44/1.64  #BackRed      : 14
% 3.44/1.64  
% 3.44/1.64  #Partial instantiations: 0
% 3.44/1.64  #Strategies tried      : 1
% 3.44/1.64  
% 3.44/1.64  Timing (in seconds)
% 3.44/1.64  ----------------------
% 3.44/1.65  Preprocessing        : 0.31
% 3.44/1.65  Parsing              : 0.16
% 3.44/1.65  CNF conversion       : 0.02
% 3.44/1.65  Main loop            : 0.48
% 3.44/1.65  Inferencing          : 0.16
% 3.44/1.65  Reduction            : 0.20
% 3.59/1.65  Demodulation         : 0.16
% 3.59/1.65  BG Simplification    : 0.02
% 3.59/1.65  Subsumption          : 0.07
% 3.59/1.65  Abstraction          : 0.03
% 3.59/1.65  MUC search           : 0.00
% 3.59/1.65  Cooper               : 0.00
% 3.59/1.65  Total                : 0.82
% 3.59/1.65  Index Insertion      : 0.00
% 3.59/1.65  Index Deletion       : 0.00
% 3.59/1.65  Index Matching       : 0.00
% 3.59/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
