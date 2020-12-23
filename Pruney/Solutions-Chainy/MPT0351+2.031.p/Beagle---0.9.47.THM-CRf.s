%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:41 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   84 (  97 expanded)
%              Number of leaves         :   43 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 106 expanded)
%              Number of equality atoms :   41 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_80,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    ! [A_54] : k2_subset_1(A_54) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_55] : m1_subset_1(k2_subset_1(A_55),k1_zfmisc_1(A_55)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65,plain,(
    ! [A_55] : m1_subset_1(A_55,k1_zfmisc_1(A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56])).

tff(c_976,plain,(
    ! [A_172,B_173,C_174] :
      ( k4_subset_1(A_172,B_173,C_174) = k2_xboole_0(B_173,C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_983,plain,(
    ! [A_175,B_176] :
      ( k4_subset_1(A_175,B_176,A_175) = k2_xboole_0(B_176,A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175)) ) ),
    inference(resolution,[status(thm)],[c_65,c_976])).

tff(c_990,plain,(
    k4_subset_1('#skF_5','#skF_6','#skF_5') = k2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_983])).

tff(c_62,plain,(
    k4_subset_1('#skF_5','#skF_6',k2_subset_1('#skF_5')) != k2_subset_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_66,plain,(
    k4_subset_1('#skF_5','#skF_6','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_62])).

tff(c_1000,plain,(
    k2_xboole_0('#skF_6','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_990,c_66])).

tff(c_38,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_154,plain,(
    ! [B_76,A_77] : k3_tarski(k2_tarski(B_76,A_77)) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_138])).

tff(c_52,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_160,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_52])).

tff(c_32,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_356,plain,(
    ! [D_97,A_98,B_99] :
      ( r2_hidden(D_97,A_98)
      | ~ r2_hidden(D_97,k4_xboole_0(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_369,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_98,B_99)),A_98)
      | k4_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_356])).

tff(c_262,plain,(
    ! [D_81,B_82,A_83] :
      ( ~ r2_hidden(D_81,B_82)
      | ~ r2_hidden(D_81,k4_xboole_0(A_83,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_570,plain,(
    ! [A_122,B_123] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_122,B_123)),B_123)
      | k4_xboole_0(A_122,B_123) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_262])).

tff(c_585,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_369,c_570])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_289,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_298,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_289])).

tff(c_589,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_298])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_530,plain,(
    ! [C_117,A_118,B_119] :
      ( r2_hidden(C_117,A_118)
      | ~ r2_hidden(C_117,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1592,plain,(
    ! [A_235,B_236,A_237] :
      ( r2_hidden('#skF_1'(A_235,B_236),A_237)
      | ~ m1_subset_1(A_235,k1_zfmisc_1(A_237))
      | r1_tarski(A_235,B_236) ) ),
    inference(resolution,[status(thm)],[c_6,c_530])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1632,plain,(
    ! [A_238,A_239] :
      ( ~ m1_subset_1(A_238,k1_zfmisc_1(A_239))
      | r1_tarski(A_238,A_239) ) ),
    inference(resolution,[status(thm)],[c_1592,c_4])).

tff(c_1641,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1632])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1645,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1641,c_34])).

tff(c_30,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1649,plain,(
    k5_xboole_0('#skF_6','#skF_6') = k4_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_30])).

tff(c_1652,plain,(
    k4_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_1649])).

tff(c_36,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1712,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1652,c_36])).

tff(c_1733,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_32,c_1712])).

tff(c_1735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:33:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.55  
% 3.49/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 3.49/1.55  
% 3.49/1.55  %Foreground sorts:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Background operators:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Foreground operators:
% 3.49/1.55  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.49/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.49/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.49/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.55  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.49/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.49/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.49/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.49/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.49/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.49/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.55  
% 3.60/1.57  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.60/1.57  tff(f_80, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.60/1.57  tff(f_82, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.60/1.57  tff(f_95, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.60/1.57  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.60/1.57  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.60/1.57  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.60/1.57  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.60/1.57  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.60/1.57  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.60/1.57  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.60/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.60/1.57  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.60/1.57  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.60/1.57  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.60/1.57  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.60/1.57  tff(c_54, plain, (![A_54]: (k2_subset_1(A_54)=A_54)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.60/1.57  tff(c_56, plain, (![A_55]: (m1_subset_1(k2_subset_1(A_55), k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.60/1.57  tff(c_65, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56])).
% 3.60/1.57  tff(c_976, plain, (![A_172, B_173, C_174]: (k4_subset_1(A_172, B_173, C_174)=k2_xboole_0(B_173, C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | ~m1_subset_1(B_173, k1_zfmisc_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.60/1.57  tff(c_983, plain, (![A_175, B_176]: (k4_subset_1(A_175, B_176, A_175)=k2_xboole_0(B_176, A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)))), inference(resolution, [status(thm)], [c_65, c_976])).
% 3.60/1.57  tff(c_990, plain, (k4_subset_1('#skF_5', '#skF_6', '#skF_5')=k2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_983])).
% 3.60/1.57  tff(c_62, plain, (k4_subset_1('#skF_5', '#skF_6', k2_subset_1('#skF_5'))!=k2_subset_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.60/1.57  tff(c_66, plain, (k4_subset_1('#skF_5', '#skF_6', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_62])).
% 3.60/1.57  tff(c_1000, plain, (k2_xboole_0('#skF_6', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_990, c_66])).
% 3.60/1.57  tff(c_38, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.60/1.57  tff(c_138, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.60/1.57  tff(c_154, plain, (![B_76, A_77]: (k3_tarski(k2_tarski(B_76, A_77))=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_38, c_138])).
% 3.60/1.57  tff(c_52, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.60/1.57  tff(c_160, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_154, c_52])).
% 3.60/1.57  tff(c_32, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.60/1.57  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.60/1.57  tff(c_356, plain, (![D_97, A_98, B_99]: (r2_hidden(D_97, A_98) | ~r2_hidden(D_97, k4_xboole_0(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.60/1.57  tff(c_369, plain, (![A_98, B_99]: (r2_hidden('#skF_4'(k4_xboole_0(A_98, B_99)), A_98) | k4_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_356])).
% 3.60/1.57  tff(c_262, plain, (![D_81, B_82, A_83]: (~r2_hidden(D_81, B_82) | ~r2_hidden(D_81, k4_xboole_0(A_83, B_82)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.60/1.57  tff(c_570, plain, (![A_122, B_123]: (~r2_hidden('#skF_4'(k4_xboole_0(A_122, B_123)), B_123) | k4_xboole_0(A_122, B_123)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_262])).
% 3.60/1.57  tff(c_585, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_369, c_570])).
% 3.60/1.57  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.60/1.57  tff(c_289, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.60/1.57  tff(c_298, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_289])).
% 3.60/1.57  tff(c_589, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_585, c_298])).
% 3.60/1.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.57  tff(c_530, plain, (![C_117, A_118, B_119]: (r2_hidden(C_117, A_118) | ~r2_hidden(C_117, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.60/1.57  tff(c_1592, plain, (![A_235, B_236, A_237]: (r2_hidden('#skF_1'(A_235, B_236), A_237) | ~m1_subset_1(A_235, k1_zfmisc_1(A_237)) | r1_tarski(A_235, B_236))), inference(resolution, [status(thm)], [c_6, c_530])).
% 3.60/1.57  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.57  tff(c_1632, plain, (![A_238, A_239]: (~m1_subset_1(A_238, k1_zfmisc_1(A_239)) | r1_tarski(A_238, A_239))), inference(resolution, [status(thm)], [c_1592, c_4])).
% 3.60/1.57  tff(c_1641, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_1632])).
% 3.60/1.57  tff(c_34, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.60/1.57  tff(c_1645, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1641, c_34])).
% 3.60/1.57  tff(c_30, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.60/1.57  tff(c_1649, plain, (k5_xboole_0('#skF_6', '#skF_6')=k4_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1645, c_30])).
% 3.60/1.57  tff(c_1652, plain, (k4_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_589, c_1649])).
% 3.60/1.57  tff(c_36, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.60/1.57  tff(c_1712, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1652, c_36])).
% 3.60/1.57  tff(c_1733, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_32, c_1712])).
% 3.60/1.57  tff(c_1735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_1733])).
% 3.60/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.57  
% 3.60/1.57  Inference rules
% 3.60/1.57  ----------------------
% 3.60/1.57  #Ref     : 0
% 3.60/1.57  #Sup     : 391
% 3.60/1.57  #Fact    : 0
% 3.60/1.57  #Define  : 0
% 3.60/1.57  #Split   : 0
% 3.60/1.57  #Chain   : 0
% 3.60/1.57  #Close   : 0
% 3.60/1.57  
% 3.60/1.57  Ordering : KBO
% 3.60/1.57  
% 3.60/1.57  Simplification rules
% 3.60/1.57  ----------------------
% 3.60/1.57  #Subsume      : 60
% 3.60/1.57  #Demod        : 191
% 3.60/1.57  #Tautology    : 215
% 3.60/1.57  #SimpNegUnit  : 1
% 3.60/1.57  #BackRed      : 3
% 3.60/1.57  
% 3.60/1.57  #Partial instantiations: 0
% 3.60/1.57  #Strategies tried      : 1
% 3.60/1.57  
% 3.60/1.57  Timing (in seconds)
% 3.60/1.57  ----------------------
% 3.60/1.57  Preprocessing        : 0.32
% 3.60/1.57  Parsing              : 0.17
% 3.60/1.57  CNF conversion       : 0.02
% 3.60/1.57  Main loop            : 0.47
% 3.60/1.57  Inferencing          : 0.18
% 3.60/1.57  Reduction            : 0.15
% 3.60/1.57  Demodulation         : 0.11
% 3.60/1.57  BG Simplification    : 0.02
% 3.60/1.57  Subsumption          : 0.09
% 3.60/1.57  Abstraction          : 0.03
% 3.60/1.57  MUC search           : 0.00
% 3.60/1.57  Cooper               : 0.00
% 3.60/1.57  Total                : 0.83
% 3.60/1.57  Index Insertion      : 0.00
% 3.60/1.57  Index Deletion       : 0.00
% 3.60/1.57  Index Matching       : 0.00
% 3.60/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
