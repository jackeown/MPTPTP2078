%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:28 EST 2020

% Result     : Theorem 22.69s
% Output     : CNFRefutation 22.69s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 333 expanded)
%              Number of leaves         :   48 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 ( 392 expanded)
%              Number of equality atoms :   60 ( 260 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_99,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_84,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_66,plain,(
    ! [A_64] : k2_subset_1(A_64) = A_64 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_74,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_77,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74])).

tff(c_14,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,(
    ! [A_67] : ~ v1_xboole_0(k1_zfmisc_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_359,plain,(
    ! [B_113,A_114] :
      ( r2_hidden(B_113,A_114)
      | ~ m1_subset_1(B_113,A_114)
      | v1_xboole_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [C_59,A_55] :
      ( r1_tarski(C_59,A_55)
      | ~ r2_hidden(C_59,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_366,plain,(
    ! [B_113,A_55] :
      ( r1_tarski(B_113,A_55)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_55))
      | v1_xboole_0(k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_359,c_44])).

tff(c_653,plain,(
    ! [B_128,A_129] :
      ( r1_tarski(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_129)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_366])).

tff(c_678,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_653])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_747,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_678,c_20])).

tff(c_30,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_225,plain,(
    ! [A_98,B_99] : k3_tarski(k2_tarski(A_98,B_99)) = k2_xboole_0(B_99,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_159])).

tff(c_56,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_231,plain,(
    ! [B_99,A_98] : k2_xboole_0(B_99,A_98) = k2_xboole_0(A_98,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_56])).

tff(c_790,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_231])).

tff(c_613,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(A_126,B_127) = k3_subset_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_638,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_613])).

tff(c_22,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_648,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_22])).

tff(c_651,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_648])).

tff(c_873,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_651])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_679,plain,(
    ! [A_130,B_131] : k5_xboole_0(k5_xboole_0(A_130,B_131),k2_xboole_0(A_130,B_131)) = k3_xboole_0(A_130,B_131) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_731,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_23,A_23)) = k3_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_679])).

tff(c_739,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_731])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_535,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k5_xboole_0(A_122,B_123),C_124) = k5_xboole_0(A_122,k5_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_883,plain,(
    ! [A_139,B_140] : k5_xboole_0(A_139,k5_xboole_0(B_140,k5_xboole_0(A_139,B_140))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_535])).

tff(c_950,plain,(
    ! [A_141] : k5_xboole_0(A_141,k5_xboole_0(A_141,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_883])).

tff(c_969,plain,(
    ! [A_141,C_22] : k5_xboole_0(A_141,k5_xboole_0(k5_xboole_0(A_141,k1_xboole_0),C_22)) = k5_xboole_0(k1_xboole_0,C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_24])).

tff(c_1039,plain,(
    ! [A_145,C_146] : k5_xboole_0(A_145,k5_xboole_0(A_145,C_146)) = C_146 ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_739,c_24,c_969])).

tff(c_1109,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1039])).

tff(c_569,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k5_xboole_0(B_123,k5_xboole_0(A_122,B_123))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_535])).

tff(c_1082,plain,(
    ! [B_123,A_122] : k5_xboole_0(B_123,k5_xboole_0(A_122,B_123)) = k5_xboole_0(A_122,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_1039])).

tff(c_1537,plain,(
    ! [B_158,A_159] : k5_xboole_0(B_158,k5_xboole_0(A_159,B_158)) = A_159 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1082])).

tff(c_1533,plain,(
    ! [B_123,A_122] : k5_xboole_0(B_123,k5_xboole_0(A_122,B_123)) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1082])).

tff(c_1540,plain,(
    ! [A_159,B_158] : k5_xboole_0(k5_xboole_0(A_159,B_158),A_159) = B_158 ),
    inference(superposition,[status(thm),theory(equality)],[c_1537,c_1533])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k2_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_827,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_28])).

tff(c_2077,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_827])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1009,plain,(
    ! [A_142,C_143,B_144] :
      ( r1_tarski(k5_xboole_0(A_142,C_143),B_144)
      | ~ r1_tarski(C_143,B_144)
      | ~ r1_tarski(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5556,plain,(
    ! [A_257,B_258,B_259] :
      ( r1_tarski(k4_xboole_0(A_257,B_258),B_259)
      | ~ r1_tarski(k3_xboole_0(A_257,B_258),B_259)
      | ~ r1_tarski(A_257,B_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1009])).

tff(c_5604,plain,(
    ! [B_259] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),B_259)
      | ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),B_259)
      | ~ r1_tarski('#skF_4',B_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_5556])).

tff(c_5631,plain,(
    ! [B_259] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),B_259)
      | ~ r1_tarski('#skF_5',B_259)
      | ~ r1_tarski('#skF_4',B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2077,c_5604])).

tff(c_46,plain,(
    ! [C_59,A_55] :
      ( r2_hidden(C_59,k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_59,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_305,plain,(
    ! [B_103,A_104] :
      ( m1_subset_1(B_103,A_104)
      | ~ r2_hidden(B_103,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_308,plain,(
    ! [C_59,A_55] :
      ( m1_subset_1(C_59,k1_zfmisc_1(A_55))
      | v1_xboole_0(k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_59,A_55) ) ),
    inference(resolution,[status(thm)],[c_46,c_305])).

tff(c_314,plain,(
    ! [C_59,A_55] :
      ( m1_subset_1(C_59,k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_59,A_55) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_308])).

tff(c_2359,plain,(
    ! [A_172,B_173,C_174] :
      ( k4_subset_1(A_172,B_173,C_174) = k2_xboole_0(B_173,C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_64755,plain,(
    ! [A_490,B_491,C_492] :
      ( k4_subset_1(A_490,B_491,C_492) = k2_xboole_0(B_491,C_492)
      | ~ m1_subset_1(B_491,k1_zfmisc_1(A_490))
      | ~ r1_tarski(C_492,A_490) ) ),
    inference(resolution,[status(thm)],[c_314,c_2359])).

tff(c_64840,plain,(
    ! [C_494] :
      ( k4_subset_1('#skF_4','#skF_5',C_494) = k2_xboole_0('#skF_5',C_494)
      | ~ r1_tarski(C_494,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_64755])).

tff(c_64858,plain,
    ( k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5631,c_64840])).

tff(c_64893,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_678,c_873,c_64858])).

tff(c_64895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_64893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.69/15.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.69/15.67  
% 22.69/15.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.69/15.67  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 22.69/15.67  
% 22.69/15.67  %Foreground sorts:
% 22.69/15.67  
% 22.69/15.67  
% 22.69/15.67  %Background operators:
% 22.69/15.67  
% 22.69/15.67  
% 22.69/15.67  %Foreground operators:
% 22.69/15.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.69/15.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.69/15.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.69/15.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.69/15.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.69/15.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.69/15.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.69/15.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.69/15.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.69/15.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.69/15.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.69/15.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 22.69/15.67  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 22.69/15.67  tff('#skF_5', type, '#skF_5': $i).
% 22.69/15.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.69/15.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.69/15.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.69/15.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 22.69/15.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.69/15.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.69/15.67  tff('#skF_4', type, '#skF_4': $i).
% 22.69/15.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.69/15.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.69/15.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.69/15.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.69/15.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 22.69/15.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 22.69/15.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.69/15.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.69/15.67  
% 22.69/15.69  tff(f_99, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 22.69/15.69  tff(f_117, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 22.69/15.69  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.69/15.69  tff(f_106, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 22.69/15.69  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 22.69/15.69  tff(f_82, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 22.69/15.69  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 22.69/15.69  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 22.69/15.69  tff(f_84, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 22.69/15.69  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 22.69/15.69  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 22.69/15.69  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 22.69/15.69  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 22.69/15.69  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 22.69/15.69  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 22.69/15.69  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 22.69/15.69  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 22.69/15.69  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 22.69/15.69  tff(f_112, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 22.69/15.69  tff(c_66, plain, (![A_64]: (k2_subset_1(A_64)=A_64)), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.69/15.69  tff(c_74, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 22.69/15.69  tff(c_77, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74])).
% 22.69/15.69  tff(c_14, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.69/15.69  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 22.69/15.69  tff(c_70, plain, (![A_67]: (~v1_xboole_0(k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 22.69/15.69  tff(c_359, plain, (![B_113, A_114]: (r2_hidden(B_113, A_114) | ~m1_subset_1(B_113, A_114) | v1_xboole_0(A_114))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.69/15.69  tff(c_44, plain, (![C_59, A_55]: (r1_tarski(C_59, A_55) | ~r2_hidden(C_59, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.69/15.69  tff(c_366, plain, (![B_113, A_55]: (r1_tarski(B_113, A_55) | ~m1_subset_1(B_113, k1_zfmisc_1(A_55)) | v1_xboole_0(k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_359, c_44])).
% 22.69/15.69  tff(c_653, plain, (![B_128, A_129]: (r1_tarski(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(A_129)))), inference(negUnitSimplification, [status(thm)], [c_70, c_366])).
% 22.69/15.69  tff(c_678, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_653])).
% 22.69/15.69  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.69/15.69  tff(c_747, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_678, c_20])).
% 22.69/15.69  tff(c_30, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.69/15.69  tff(c_159, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_84])).
% 22.69/15.69  tff(c_225, plain, (![A_98, B_99]: (k3_tarski(k2_tarski(A_98, B_99))=k2_xboole_0(B_99, A_98))), inference(superposition, [status(thm), theory('equality')], [c_30, c_159])).
% 22.69/15.69  tff(c_56, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_84])).
% 22.69/15.69  tff(c_231, plain, (![B_99, A_98]: (k2_xboole_0(B_99, A_98)=k2_xboole_0(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_225, c_56])).
% 22.69/15.69  tff(c_790, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_747, c_231])).
% 22.69/15.69  tff(c_613, plain, (![A_126, B_127]: (k4_xboole_0(A_126, B_127)=k3_subset_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 22.69/15.69  tff(c_638, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_613])).
% 22.69/15.69  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.69/15.69  tff(c_648, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_638, c_22])).
% 22.69/15.69  tff(c_651, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_648])).
% 22.69/15.69  tff(c_873, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_790, c_651])).
% 22.69/15.69  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.69/15.69  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.69/15.69  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.69/15.69  tff(c_679, plain, (![A_130, B_131]: (k5_xboole_0(k5_xboole_0(A_130, B_131), k2_xboole_0(A_130, B_131))=k3_xboole_0(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.69/15.69  tff(c_731, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_23, A_23))=k3_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_26, c_679])).
% 22.69/15.69  tff(c_739, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_731])).
% 22.69/15.69  tff(c_24, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.69/15.69  tff(c_535, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k5_xboole_0(A_122, B_123), C_124)=k5_xboole_0(A_122, k5_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.69/15.69  tff(c_883, plain, (![A_139, B_140]: (k5_xboole_0(A_139, k5_xboole_0(B_140, k5_xboole_0(A_139, B_140)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_535])).
% 22.69/15.69  tff(c_950, plain, (![A_141]: (k5_xboole_0(A_141, k5_xboole_0(A_141, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_739, c_883])).
% 22.69/15.69  tff(c_969, plain, (![A_141, C_22]: (k5_xboole_0(A_141, k5_xboole_0(k5_xboole_0(A_141, k1_xboole_0), C_22))=k5_xboole_0(k1_xboole_0, C_22))), inference(superposition, [status(thm), theory('equality')], [c_950, c_24])).
% 22.69/15.69  tff(c_1039, plain, (![A_145, C_146]: (k5_xboole_0(A_145, k5_xboole_0(A_145, C_146))=C_146)), inference(demodulation, [status(thm), theory('equality')], [c_739, c_739, c_24, c_969])).
% 22.69/15.69  tff(c_1109, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_26, c_1039])).
% 22.69/15.69  tff(c_569, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k5_xboole_0(B_123, k5_xboole_0(A_122, B_123)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_535])).
% 22.69/15.69  tff(c_1082, plain, (![B_123, A_122]: (k5_xboole_0(B_123, k5_xboole_0(A_122, B_123))=k5_xboole_0(A_122, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_569, c_1039])).
% 22.69/15.69  tff(c_1537, plain, (![B_158, A_159]: (k5_xboole_0(B_158, k5_xboole_0(A_159, B_158))=A_159)), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1082])).
% 22.69/15.69  tff(c_1533, plain, (![B_123, A_122]: (k5_xboole_0(B_123, k5_xboole_0(A_122, B_123))=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1082])).
% 22.69/15.69  tff(c_1540, plain, (![A_159, B_158]: (k5_xboole_0(k5_xboole_0(A_159, B_158), A_159)=B_158)), inference(superposition, [status(thm), theory('equality')], [c_1537, c_1533])).
% 22.69/15.69  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k2_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.69/15.69  tff(c_827, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_790, c_28])).
% 22.69/15.69  tff(c_2077, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_827])).
% 22.69/15.69  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.69/15.69  tff(c_1009, plain, (![A_142, C_143, B_144]: (r1_tarski(k5_xboole_0(A_142, C_143), B_144) | ~r1_tarski(C_143, B_144) | ~r1_tarski(A_142, B_144))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.69/15.69  tff(c_5556, plain, (![A_257, B_258, B_259]: (r1_tarski(k4_xboole_0(A_257, B_258), B_259) | ~r1_tarski(k3_xboole_0(A_257, B_258), B_259) | ~r1_tarski(A_257, B_259))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1009])).
% 22.69/15.69  tff(c_5604, plain, (![B_259]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), B_259) | ~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), B_259) | ~r1_tarski('#skF_4', B_259))), inference(superposition, [status(thm), theory('equality')], [c_638, c_5556])).
% 22.69/15.69  tff(c_5631, plain, (![B_259]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), B_259) | ~r1_tarski('#skF_5', B_259) | ~r1_tarski('#skF_4', B_259))), inference(demodulation, [status(thm), theory('equality')], [c_2077, c_5604])).
% 22.69/15.69  tff(c_46, plain, (![C_59, A_55]: (r2_hidden(C_59, k1_zfmisc_1(A_55)) | ~r1_tarski(C_59, A_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.69/15.69  tff(c_305, plain, (![B_103, A_104]: (m1_subset_1(B_103, A_104) | ~r2_hidden(B_103, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.69/15.69  tff(c_308, plain, (![C_59, A_55]: (m1_subset_1(C_59, k1_zfmisc_1(A_55)) | v1_xboole_0(k1_zfmisc_1(A_55)) | ~r1_tarski(C_59, A_55))), inference(resolution, [status(thm)], [c_46, c_305])).
% 22.69/15.69  tff(c_314, plain, (![C_59, A_55]: (m1_subset_1(C_59, k1_zfmisc_1(A_55)) | ~r1_tarski(C_59, A_55))), inference(negUnitSimplification, [status(thm)], [c_70, c_308])).
% 22.69/15.69  tff(c_2359, plain, (![A_172, B_173, C_174]: (k4_subset_1(A_172, B_173, C_174)=k2_xboole_0(B_173, C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | ~m1_subset_1(B_173, k1_zfmisc_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.69/15.69  tff(c_64755, plain, (![A_490, B_491, C_492]: (k4_subset_1(A_490, B_491, C_492)=k2_xboole_0(B_491, C_492) | ~m1_subset_1(B_491, k1_zfmisc_1(A_490)) | ~r1_tarski(C_492, A_490))), inference(resolution, [status(thm)], [c_314, c_2359])).
% 22.69/15.69  tff(c_64840, plain, (![C_494]: (k4_subset_1('#skF_4', '#skF_5', C_494)=k2_xboole_0('#skF_5', C_494) | ~r1_tarski(C_494, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_64755])).
% 22.69/15.69  tff(c_64858, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5631, c_64840])).
% 22.69/15.69  tff(c_64893, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_678, c_873, c_64858])).
% 22.69/15.69  tff(c_64895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_64893])).
% 22.69/15.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.69/15.69  
% 22.69/15.69  Inference rules
% 22.69/15.69  ----------------------
% 22.69/15.69  #Ref     : 0
% 22.69/15.69  #Sup     : 16948
% 22.69/15.69  #Fact    : 0
% 22.69/15.69  #Define  : 0
% 22.69/15.69  #Split   : 3
% 22.69/15.69  #Chain   : 0
% 22.69/15.69  #Close   : 0
% 22.69/15.69  
% 22.69/15.69  Ordering : KBO
% 22.69/15.69  
% 22.69/15.69  Simplification rules
% 22.69/15.69  ----------------------
% 22.69/15.69  #Subsume      : 1214
% 22.69/15.69  #Demod        : 25587
% 22.69/15.69  #Tautology    : 5861
% 22.69/15.69  #SimpNegUnit  : 22
% 22.69/15.69  #BackRed      : 11
% 22.69/15.69  
% 22.69/15.69  #Partial instantiations: 0
% 22.69/15.69  #Strategies tried      : 1
% 22.69/15.69  
% 22.69/15.69  Timing (in seconds)
% 22.69/15.69  ----------------------
% 22.69/15.69  Preprocessing        : 0.34
% 22.69/15.69  Parsing              : 0.17
% 22.69/15.69  CNF conversion       : 0.02
% 22.69/15.69  Main loop            : 14.58
% 22.69/15.69  Inferencing          : 1.44
% 22.69/15.69  Reduction            : 10.70
% 22.69/15.69  Demodulation         : 10.15
% 22.69/15.69  BG Simplification    : 0.25
% 22.69/15.69  Subsumption          : 1.84
% 22.69/15.69  Abstraction          : 0.41
% 22.69/15.69  MUC search           : 0.00
% 22.69/15.69  Cooper               : 0.00
% 22.69/15.69  Total                : 14.95
% 22.69/15.69  Index Insertion      : 0.00
% 22.69/15.69  Index Deletion       : 0.00
% 22.69/15.69  Index Matching       : 0.00
% 22.69/15.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
