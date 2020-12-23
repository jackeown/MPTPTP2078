%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:38 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 262 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          :  105 ( 273 expanded)
%              Number of equality atoms :   70 ( 222 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_60,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_28] : k2_subset_1(A_28) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_29] : m1_subset_1(k2_subset_1(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_43,plain,(
    ! [A_29] : m1_subset_1(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_772,plain,(
    ! [A_85,B_86,C_87] :
      ( k4_subset_1(A_85,B_86,C_87) = k2_xboole_0(B_86,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2323,plain,(
    ! [A_121,B_122] :
      ( k4_subset_1(A_121,B_122,A_121) = k2_xboole_0(B_122,A_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(resolution,[status(thm)],[c_43,c_772])).

tff(c_2330,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_2323])).

tff(c_40,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_40])).

tff(c_2334,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_44])).

tff(c_26,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_159,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_183,plain,(
    ! [B_52,A_53] : k3_tarski(k2_tarski(B_52,A_53)) = k2_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_159])).

tff(c_30,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_189,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_366,plain,(
    ! [A_64,B_65] : k2_xboole_0(k3_xboole_0(A_64,B_65),k4_xboole_0(A_64,B_65)) = A_64 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_399,plain,(
    ! [A_66] : k2_xboole_0(k3_xboole_0(A_66,k1_xboole_0),A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_366])).

tff(c_478,plain,(
    ! [A_71] : k2_xboole_0(k3_xboole_0(k1_xboole_0,A_71),A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_399])).

tff(c_514,plain,(
    ! [A_53] : k2_xboole_0(A_53,k3_xboole_0(k1_xboole_0,A_53)) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_478])).

tff(c_206,plain,(
    ! [B_54,A_55] : k2_xboole_0(B_54,A_55) = k2_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_30])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_222,plain,(
    ! [A_55] : k2_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_14])).

tff(c_569,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k4_xboole_0(B_74,A_73)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_584,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = k2_xboole_0(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_569])).

tff(c_591,plain,(
    ! [A_75] : k5_xboole_0(k1_xboole_0,A_75) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_584])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_799,plain,(
    ! [B_89] : k4_xboole_0(k1_xboole_0,B_89) = k3_xboole_0(k1_xboole_0,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_12])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1821,plain,(
    ! [B_111] : k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_111)) = k3_xboole_0(k1_xboole_0,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_20])).

tff(c_387,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_366])).

tff(c_1848,plain,(
    ! [B_111] : k2_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,B_111),k1_xboole_0),k3_xboole_0(k1_xboole_0,B_111)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1821,c_387])).

tff(c_1911,plain,(
    ! [B_111] : k3_xboole_0(k1_xboole_0,B_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_189,c_2,c_1848])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_320,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_335,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_320])).

tff(c_578,plain,(
    ! [A_15] : k5_xboole_0(A_15,k3_xboole_0(A_15,k1_xboole_0)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_569])).

tff(c_618,plain,(
    ! [A_76] : k5_xboole_0(A_76,k3_xboole_0(A_76,k1_xboole_0)) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_578])).

tff(c_647,plain,(
    ! [A_1] : k5_xboole_0(A_1,k3_xboole_0(k1_xboole_0,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_618])).

tff(c_1931,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_647])).

tff(c_602,plain,(
    ! [B_11] : k4_xboole_0(k1_xboole_0,B_11) = k3_xboole_0(k1_xboole_0,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_12])).

tff(c_1930,plain,(
    ! [B_11] : k4_xboole_0(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_602])).

tff(c_304,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_897,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(B_93,A_92)) = k4_xboole_0(A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_304])).

tff(c_589,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_584])).

tff(c_912,plain,(
    ! [B_93] : k4_xboole_0(k1_xboole_0,B_93) = k3_xboole_0(B_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_589])).

tff(c_2051,plain,(
    ! [B_93] : k3_xboole_0(B_93,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_912])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_444,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_1'(A_67,B_68),B_68)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_450,plain,(
    ! [A_69] : r1_tarski(A_69,A_69) ),
    inference(resolution,[status(thm)],[c_8,c_444])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_456,plain,(
    ! [A_70] : k3_xboole_0(A_70,A_70) = A_70 ),
    inference(resolution,[status(thm)],[c_450,c_16])).

tff(c_469,plain,(
    ! [A_70] : k5_xboole_0(A_70,A_70) = k4_xboole_0(A_70,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_12])).

tff(c_476,plain,(
    ! [A_70] : k5_xboole_0(A_70,A_70) = k3_xboole_0(A_70,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_469])).

tff(c_2170,plain,(
    ! [A_70] : k5_xboole_0(A_70,A_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_476])).

tff(c_765,plain,(
    ! [C_82,A_83,B_84] :
      ( r2_hidden(C_82,A_83)
      | ~ r2_hidden(C_82,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2351,plain,(
    ! [A_124,B_125,A_126] :
      ( r2_hidden('#skF_1'(A_124,B_125),A_126)
      | ~ m1_subset_1(A_124,k1_zfmisc_1(A_126))
      | r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_8,c_765])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2364,plain,(
    ! [A_127,A_128] :
      ( ~ m1_subset_1(A_127,k1_zfmisc_1(A_128))
      | r1_tarski(A_127,A_128) ) ),
    inference(resolution,[status(thm)],[c_2351,c_6])).

tff(c_2373,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_2364])).

tff(c_2377,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2373,c_16])).

tff(c_2396,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2377,c_12])).

tff(c_2400,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2170,c_2396])).

tff(c_24,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2411,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2400,c_24])).

tff(c_2422,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1931,c_189,c_2411])).

tff(c_2424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2334,c_2422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.57  
% 3.48/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.57  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.57  
% 3.48/1.57  %Foreground sorts:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Background operators:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Foreground operators:
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.57  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.48/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.48/1.57  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.48/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.57  
% 3.48/1.59  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.48/1.59  tff(f_60, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.48/1.59  tff(f_62, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.48/1.59  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.48/1.59  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.48/1.59  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.48/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.48/1.59  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.48/1.59  tff(f_50, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.48/1.59  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.48/1.59  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.48/1.59  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.48/1.59  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.48/1.59  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.48/1.59  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.48/1.59  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.48/1.59  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.48/1.59  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.59  tff(c_32, plain, (![A_28]: (k2_subset_1(A_28)=A_28)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.48/1.59  tff(c_34, plain, (![A_29]: (m1_subset_1(k2_subset_1(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.48/1.59  tff(c_43, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.48/1.59  tff(c_772, plain, (![A_85, B_86, C_87]: (k4_subset_1(A_85, B_86, C_87)=k2_xboole_0(B_86, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(A_85)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.48/1.59  tff(c_2323, plain, (![A_121, B_122]: (k4_subset_1(A_121, B_122, A_121)=k2_xboole_0(B_122, A_121) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(resolution, [status(thm)], [c_43, c_772])).
% 3.48/1.59  tff(c_2330, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_2323])).
% 3.48/1.59  tff(c_40, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.59  tff(c_44, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_40])).
% 3.48/1.59  tff(c_2334, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2330, c_44])).
% 3.48/1.59  tff(c_26, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.48/1.59  tff(c_159, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.59  tff(c_183, plain, (![B_52, A_53]: (k3_tarski(k2_tarski(B_52, A_53))=k2_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_26, c_159])).
% 3.48/1.59  tff(c_30, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.59  tff(c_189, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_183, c_30])).
% 3.48/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.59  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.48/1.59  tff(c_366, plain, (![A_64, B_65]: (k2_xboole_0(k3_xboole_0(A_64, B_65), k4_xboole_0(A_64, B_65))=A_64)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.59  tff(c_399, plain, (![A_66]: (k2_xboole_0(k3_xboole_0(A_66, k1_xboole_0), A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_18, c_366])).
% 3.48/1.59  tff(c_478, plain, (![A_71]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, A_71), A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_2, c_399])).
% 3.48/1.59  tff(c_514, plain, (![A_53]: (k2_xboole_0(A_53, k3_xboole_0(k1_xboole_0, A_53))=A_53)), inference(superposition, [status(thm), theory('equality')], [c_189, c_478])).
% 3.48/1.59  tff(c_206, plain, (![B_54, A_55]: (k2_xboole_0(B_54, A_55)=k2_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_183, c_30])).
% 3.48/1.59  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.59  tff(c_222, plain, (![A_55]: (k2_xboole_0(k1_xboole_0, A_55)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_206, c_14])).
% 3.48/1.59  tff(c_569, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k4_xboole_0(B_74, A_73))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.48/1.59  tff(c_584, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=k2_xboole_0(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_569])).
% 3.48/1.59  tff(c_591, plain, (![A_75]: (k5_xboole_0(k1_xboole_0, A_75)=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_584])).
% 3.48/1.59  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.48/1.59  tff(c_799, plain, (![B_89]: (k4_xboole_0(k1_xboole_0, B_89)=k3_xboole_0(k1_xboole_0, B_89))), inference(superposition, [status(thm), theory('equality')], [c_591, c_12])).
% 3.48/1.59  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.48/1.59  tff(c_1821, plain, (![B_111]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_111))=k3_xboole_0(k1_xboole_0, B_111))), inference(superposition, [status(thm), theory('equality')], [c_799, c_20])).
% 3.48/1.59  tff(c_387, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_366])).
% 3.48/1.59  tff(c_1848, plain, (![B_111]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0, B_111), k1_xboole_0), k3_xboole_0(k1_xboole_0, B_111))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1821, c_387])).
% 3.48/1.59  tff(c_1911, plain, (![B_111]: (k3_xboole_0(k1_xboole_0, B_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_514, c_189, c_2, c_1848])).
% 3.48/1.59  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.48/1.59  tff(c_320, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.48/1.59  tff(c_335, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_320])).
% 3.48/1.59  tff(c_578, plain, (![A_15]: (k5_xboole_0(A_15, k3_xboole_0(A_15, k1_xboole_0))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_335, c_569])).
% 3.48/1.59  tff(c_618, plain, (![A_76]: (k5_xboole_0(A_76, k3_xboole_0(A_76, k1_xboole_0))=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_578])).
% 3.48/1.59  tff(c_647, plain, (![A_1]: (k5_xboole_0(A_1, k3_xboole_0(k1_xboole_0, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_618])).
% 3.48/1.59  tff(c_1931, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_1911, c_647])).
% 3.48/1.59  tff(c_602, plain, (![B_11]: (k4_xboole_0(k1_xboole_0, B_11)=k3_xboole_0(k1_xboole_0, B_11))), inference(superposition, [status(thm), theory('equality')], [c_591, c_12])).
% 3.48/1.59  tff(c_1930, plain, (![B_11]: (k4_xboole_0(k1_xboole_0, B_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1911, c_602])).
% 3.48/1.59  tff(c_304, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.48/1.59  tff(c_897, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(B_93, A_92))=k4_xboole_0(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_2, c_304])).
% 3.48/1.59  tff(c_589, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_584])).
% 3.48/1.59  tff(c_912, plain, (![B_93]: (k4_xboole_0(k1_xboole_0, B_93)=k3_xboole_0(B_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_897, c_589])).
% 3.48/1.59  tff(c_2051, plain, (![B_93]: (k3_xboole_0(B_93, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_912])).
% 3.48/1.59  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.48/1.59  tff(c_444, plain, (![A_67, B_68]: (~r2_hidden('#skF_1'(A_67, B_68), B_68) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.48/1.59  tff(c_450, plain, (![A_69]: (r1_tarski(A_69, A_69))), inference(resolution, [status(thm)], [c_8, c_444])).
% 3.48/1.59  tff(c_16, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.48/1.59  tff(c_456, plain, (![A_70]: (k3_xboole_0(A_70, A_70)=A_70)), inference(resolution, [status(thm)], [c_450, c_16])).
% 3.48/1.59  tff(c_469, plain, (![A_70]: (k5_xboole_0(A_70, A_70)=k4_xboole_0(A_70, A_70))), inference(superposition, [status(thm), theory('equality')], [c_456, c_12])).
% 3.48/1.59  tff(c_476, plain, (![A_70]: (k5_xboole_0(A_70, A_70)=k3_xboole_0(A_70, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_469])).
% 3.48/1.59  tff(c_2170, plain, (![A_70]: (k5_xboole_0(A_70, A_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2051, c_476])).
% 3.48/1.59  tff(c_765, plain, (![C_82, A_83, B_84]: (r2_hidden(C_82, A_83) | ~r2_hidden(C_82, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.48/1.59  tff(c_2351, plain, (![A_124, B_125, A_126]: (r2_hidden('#skF_1'(A_124, B_125), A_126) | ~m1_subset_1(A_124, k1_zfmisc_1(A_126)) | r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_8, c_765])).
% 3.48/1.59  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.48/1.59  tff(c_2364, plain, (![A_127, A_128]: (~m1_subset_1(A_127, k1_zfmisc_1(A_128)) | r1_tarski(A_127, A_128))), inference(resolution, [status(thm)], [c_2351, c_6])).
% 3.48/1.59  tff(c_2373, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_2364])).
% 3.48/1.59  tff(c_2377, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_2373, c_16])).
% 3.48/1.59  tff(c_2396, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2377, c_12])).
% 3.48/1.59  tff(c_2400, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2170, c_2396])).
% 3.48/1.59  tff(c_24, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.48/1.59  tff(c_2411, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2400, c_24])).
% 3.48/1.59  tff(c_2422, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1931, c_189, c_2411])).
% 3.48/1.59  tff(c_2424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2334, c_2422])).
% 3.48/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.59  
% 3.48/1.59  Inference rules
% 3.48/1.59  ----------------------
% 3.48/1.59  #Ref     : 0
% 3.48/1.59  #Sup     : 539
% 3.48/1.59  #Fact    : 0
% 3.48/1.59  #Define  : 0
% 3.48/1.59  #Split   : 0
% 3.48/1.59  #Chain   : 0
% 3.48/1.59  #Close   : 0
% 3.48/1.59  
% 3.48/1.59  Ordering : KBO
% 3.48/1.59  
% 3.48/1.59  Simplification rules
% 3.48/1.59  ----------------------
% 3.48/1.59  #Subsume      : 3
% 3.48/1.59  #Demod        : 503
% 3.48/1.59  #Tautology    : 438
% 3.48/1.59  #SimpNegUnit  : 1
% 3.48/1.59  #BackRed      : 21
% 3.48/1.59  
% 3.48/1.59  #Partial instantiations: 0
% 3.48/1.59  #Strategies tried      : 1
% 3.48/1.59  
% 3.48/1.59  Timing (in seconds)
% 3.48/1.59  ----------------------
% 3.48/1.59  Preprocessing        : 0.31
% 3.48/1.59  Parsing              : 0.17
% 3.48/1.59  CNF conversion       : 0.02
% 3.48/1.59  Main loop            : 0.51
% 3.48/1.59  Inferencing          : 0.17
% 3.48/1.59  Reduction            : 0.21
% 3.48/1.59  Demodulation         : 0.18
% 3.48/1.59  BG Simplification    : 0.02
% 3.48/1.59  Subsumption          : 0.07
% 3.48/1.59  Abstraction          : 0.03
% 3.48/1.59  MUC search           : 0.00
% 3.48/1.59  Cooper               : 0.00
% 3.48/1.59  Total                : 0.85
% 3.48/1.59  Index Insertion      : 0.00
% 3.48/1.59  Index Deletion       : 0.00
% 3.48/1.59  Index Matching       : 0.00
% 3.48/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
