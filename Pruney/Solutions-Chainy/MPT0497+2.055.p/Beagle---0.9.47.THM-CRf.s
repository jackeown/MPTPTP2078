%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:46 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 372 expanded)
%              Number of leaves         :   28 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 ( 725 expanded)
%              Number of equality atoms :   55 ( 265 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_44,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_82,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_116,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_38])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_119])).

tff(c_140,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_137])).

tff(c_83,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    k4_xboole_0(k1_relat_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_83])).

tff(c_134,plain,(
    k4_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) = k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_119])).

tff(c_236,plain,(
    k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_134])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( k3_xboole_0(k1_relat_1(B_23),A_22) = k1_relat_1(k7_relat_1(B_23,A_22))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_240,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_34])).

tff(c_247,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_240])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_617,plain,(
    ! [A_81,B_82] :
      ( k1_relat_1(k7_relat_1(A_81,B_82)) != k1_xboole_0
      | k7_relat_1(A_81,B_82) = k1_xboole_0
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_623,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_617])).

tff(c_629,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_623])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_629])).

tff(c_633,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_632,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_637,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_22])).

tff(c_641,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_637])).

tff(c_684,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_699,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_684])).

tff(c_702,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_699])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_744,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,B_100)
      | ~ r2_hidden(C_101,A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_862,plain,(
    ! [C_112,B_113,A_114] :
      ( ~ r2_hidden(C_112,B_113)
      | ~ r2_hidden(C_112,A_114)
      | k4_xboole_0(A_114,B_113) != A_114 ) ),
    inference(resolution,[status(thm)],[c_16,c_744])).

tff(c_2726,plain,(
    ! [A_203,B_204,A_205] :
      ( ~ r2_hidden('#skF_1'(A_203,B_204),A_205)
      | k4_xboole_0(A_205,A_203) != A_205
      | r1_xboole_0(A_203,B_204) ) ),
    inference(resolution,[status(thm)],[c_6,c_862])).

tff(c_2765,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_2726])).

tff(c_2787,plain,(
    ! [A_206,B_207] :
      ( k1_xboole_0 != A_206
      | r1_xboole_0(A_206,B_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_2765])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2800,plain,(
    ! [B_207] : k4_xboole_0(k1_xboole_0,B_207) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2787,c_14])).

tff(c_748,plain,(
    ! [B_102,A_103] :
      ( k3_xboole_0(k1_relat_1(B_102),A_103) = k1_relat_1(k7_relat_1(B_102,A_103))
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_759,plain,(
    ! [B_102] :
      ( k1_relat_1(k7_relat_1(B_102,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_8])).

tff(c_884,plain,(
    ! [A_119,B_120] :
      ( k1_relat_1(k7_relat_1(A_119,B_120)) != k1_xboole_0
      | k7_relat_1(A_119,B_120) = k1_xboole_0
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_897,plain,(
    ! [B_121] :
      ( k7_relat_1(B_121,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_884])).

tff(c_907,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_641,c_897])).

tff(c_947,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_759])).

tff(c_962,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_947])).

tff(c_910,plain,(
    ! [A_122,C_123,B_124] :
      ( r2_hidden(A_122,k1_relat_1(C_123))
      | ~ r2_hidden(A_122,k1_relat_1(k7_relat_1(C_123,B_124)))
      | ~ v1_relat_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_916,plain,(
    ! [A_122,B_102] :
      ( r2_hidden(A_122,k1_relat_1(B_102))
      | ~ r2_hidden(A_122,k1_xboole_0)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_910])).

tff(c_909,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_897])).

tff(c_30,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(A_19,k1_relat_1(C_21))
      | ~ r2_hidden(A_19,k1_relat_1(k7_relat_1(C_21,B_20)))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_986,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_19,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_30])).

tff(c_1017,plain,(
    ! [A_125] :
      ( r2_hidden(A_125,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_125,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_962,c_986])).

tff(c_747,plain,(
    ! [C_101,B_11,A_10] :
      ( ~ r2_hidden(C_101,B_11)
      | ~ r2_hidden(C_101,A_10)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(resolution,[status(thm)],[c_16,c_744])).

tff(c_1440,plain,(
    ! [A_148,A_149] :
      ( ~ r2_hidden(A_148,A_149)
      | k4_xboole_0(A_149,k1_relat_1('#skF_3')) != A_149
      | ~ r2_hidden(A_148,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1017,c_747])).

tff(c_1457,plain,(
    ! [B_102,A_122] :
      ( k4_xboole_0(k1_relat_1(B_102),k1_relat_1('#skF_3')) != k1_relat_1(B_102)
      | ~ r2_hidden(A_122,k1_xboole_0)
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_916,c_1440])).

tff(c_3652,plain,(
    ! [B_240] :
      ( k4_xboole_0(k1_relat_1(B_240),k1_relat_1('#skF_3')) != k1_relat_1(B_240)
      | ~ v1_relat_1(B_240) ) ),
    inference(splitLeft,[status(thm)],[c_1457])).

tff(c_3667,plain,
    ( k4_xboole_0(k1_xboole_0,k1_relat_1('#skF_3')) != k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_962,c_3652])).

tff(c_3684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_2800,c_962,c_3667])).

tff(c_3685,plain,(
    ! [A_122] : ~ r2_hidden(A_122,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1457])).

tff(c_1149,plain,(
    ! [A_130,C_131,B_132] :
      ( r2_hidden(A_130,k1_relat_1(k7_relat_1(C_131,B_132)))
      | ~ r2_hidden(A_130,k1_relat_1(C_131))
      | ~ r2_hidden(A_130,B_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1178,plain,(
    ! [A_130] :
      ( r2_hidden(A_130,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_130,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_130,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_1149])).

tff(c_1199,plain,(
    ! [A_135] :
      ( r2_hidden(A_135,k1_xboole_0)
      | ~ r2_hidden(A_135,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_135,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_962,c_1178])).

tff(c_1213,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_2),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_2),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1199])).

tff(c_3929,plain,(
    ! [B_249] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_249),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_249) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3685,c_1213])).

tff(c_3937,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_3929])).

tff(c_3942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_633,c_633,c_3937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.83  
% 4.54/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.84  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.54/1.84  
% 4.54/1.84  %Foreground sorts:
% 4.54/1.84  
% 4.54/1.84  
% 4.54/1.84  %Background operators:
% 4.54/1.84  
% 4.54/1.84  
% 4.54/1.84  %Foreground operators:
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.54/1.84  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.54/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.54/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.54/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.54/1.84  
% 4.54/1.85  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 4.54/1.85  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.54/1.85  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.54/1.85  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.54/1.85  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.54/1.85  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 4.54/1.85  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.54/1.85  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.54/1.85  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.54/1.85  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 4.54/1.85  tff(c_44, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.54/1.85  tff(c_82, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 4.54/1.85  tff(c_38, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.54/1.85  tff(c_116, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_82, c_38])).
% 4.54/1.85  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.54/1.85  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.54/1.85  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.54/1.85  tff(c_119, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.54/1.85  tff(c_137, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_119])).
% 4.54/1.85  tff(c_140, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_137])).
% 4.54/1.85  tff(c_83, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.85  tff(c_87, plain, (k4_xboole_0(k1_relat_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_83])).
% 4.54/1.85  tff(c_134, plain, (k4_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))=k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87, c_119])).
% 4.54/1.85  tff(c_236, plain, (k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_134])).
% 4.54/1.85  tff(c_34, plain, (![B_23, A_22]: (k3_xboole_0(k1_relat_1(B_23), A_22)=k1_relat_1(k7_relat_1(B_23, A_22)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.54/1.85  tff(c_240, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_236, c_34])).
% 4.54/1.85  tff(c_247, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_240])).
% 4.54/1.85  tff(c_22, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.54/1.85  tff(c_71, plain, (![A_29]: (k1_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.54/1.85  tff(c_617, plain, (![A_81, B_82]: (k1_relat_1(k7_relat_1(A_81, B_82))!=k1_xboole_0 | k7_relat_1(A_81, B_82)=k1_xboole_0 | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_22, c_71])).
% 4.54/1.85  tff(c_623, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_247, c_617])).
% 4.54/1.85  tff(c_629, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_623])).
% 4.54/1.85  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_629])).
% 4.54/1.85  tff(c_633, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.54/1.85  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.54/1.85  tff(c_632, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 4.54/1.85  tff(c_637, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_632, c_22])).
% 4.54/1.85  tff(c_641, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_637])).
% 4.54/1.85  tff(c_684, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.54/1.85  tff(c_699, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_684])).
% 4.54/1.85  tff(c_702, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_699])).
% 4.54/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.54/1.85  tff(c_16, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.85  tff(c_744, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, B_100) | ~r2_hidden(C_101, A_99))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.54/1.85  tff(c_862, plain, (![C_112, B_113, A_114]: (~r2_hidden(C_112, B_113) | ~r2_hidden(C_112, A_114) | k4_xboole_0(A_114, B_113)!=A_114)), inference(resolution, [status(thm)], [c_16, c_744])).
% 4.54/1.85  tff(c_2726, plain, (![A_203, B_204, A_205]: (~r2_hidden('#skF_1'(A_203, B_204), A_205) | k4_xboole_0(A_205, A_203)!=A_205 | r1_xboole_0(A_203, B_204))), inference(resolution, [status(thm)], [c_6, c_862])).
% 4.54/1.85  tff(c_2765, plain, (![A_1, B_2]: (k4_xboole_0(A_1, A_1)!=A_1 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_2726])).
% 4.54/1.85  tff(c_2787, plain, (![A_206, B_207]: (k1_xboole_0!=A_206 | r1_xboole_0(A_206, B_207))), inference(demodulation, [status(thm), theory('equality')], [c_702, c_2765])).
% 4.54/1.85  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.85  tff(c_2800, plain, (![B_207]: (k4_xboole_0(k1_xboole_0, B_207)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2787, c_14])).
% 4.54/1.85  tff(c_748, plain, (![B_102, A_103]: (k3_xboole_0(k1_relat_1(B_102), A_103)=k1_relat_1(k7_relat_1(B_102, A_103)) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.54/1.85  tff(c_759, plain, (![B_102]: (k1_relat_1(k7_relat_1(B_102, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_748, c_8])).
% 4.54/1.85  tff(c_884, plain, (![A_119, B_120]: (k1_relat_1(k7_relat_1(A_119, B_120))!=k1_xboole_0 | k7_relat_1(A_119, B_120)=k1_xboole_0 | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_22, c_71])).
% 4.54/1.85  tff(c_897, plain, (![B_121]: (k7_relat_1(B_121, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_121))), inference(superposition, [status(thm), theory('equality')], [c_759, c_884])).
% 4.54/1.85  tff(c_907, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_641, c_897])).
% 4.54/1.85  tff(c_947, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_907, c_759])).
% 4.54/1.85  tff(c_962, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_641, c_947])).
% 4.54/1.85  tff(c_910, plain, (![A_122, C_123, B_124]: (r2_hidden(A_122, k1_relat_1(C_123)) | ~r2_hidden(A_122, k1_relat_1(k7_relat_1(C_123, B_124))) | ~v1_relat_1(C_123))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.54/1.85  tff(c_916, plain, (![A_122, B_102]: (r2_hidden(A_122, k1_relat_1(B_102)) | ~r2_hidden(A_122, k1_xboole_0) | ~v1_relat_1(B_102) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_759, c_910])).
% 4.54/1.85  tff(c_909, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_897])).
% 4.54/1.85  tff(c_30, plain, (![A_19, C_21, B_20]: (r2_hidden(A_19, k1_relat_1(C_21)) | ~r2_hidden(A_19, k1_relat_1(k7_relat_1(C_21, B_20))) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.54/1.85  tff(c_986, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_3')) | ~r2_hidden(A_19, k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_909, c_30])).
% 4.54/1.85  tff(c_1017, plain, (![A_125]: (r2_hidden(A_125, k1_relat_1('#skF_3')) | ~r2_hidden(A_125, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_962, c_986])).
% 4.54/1.85  tff(c_747, plain, (![C_101, B_11, A_10]: (~r2_hidden(C_101, B_11) | ~r2_hidden(C_101, A_10) | k4_xboole_0(A_10, B_11)!=A_10)), inference(resolution, [status(thm)], [c_16, c_744])).
% 4.54/1.85  tff(c_1440, plain, (![A_148, A_149]: (~r2_hidden(A_148, A_149) | k4_xboole_0(A_149, k1_relat_1('#skF_3'))!=A_149 | ~r2_hidden(A_148, k1_xboole_0))), inference(resolution, [status(thm)], [c_1017, c_747])).
% 4.54/1.85  tff(c_1457, plain, (![B_102, A_122]: (k4_xboole_0(k1_relat_1(B_102), k1_relat_1('#skF_3'))!=k1_relat_1(B_102) | ~r2_hidden(A_122, k1_xboole_0) | ~v1_relat_1(B_102))), inference(resolution, [status(thm)], [c_916, c_1440])).
% 4.54/1.85  tff(c_3652, plain, (![B_240]: (k4_xboole_0(k1_relat_1(B_240), k1_relat_1('#skF_3'))!=k1_relat_1(B_240) | ~v1_relat_1(B_240))), inference(splitLeft, [status(thm)], [c_1457])).
% 4.54/1.85  tff(c_3667, plain, (k4_xboole_0(k1_xboole_0, k1_relat_1('#skF_3'))!=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_962, c_3652])).
% 4.54/1.85  tff(c_3684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_2800, c_962, c_3667])).
% 4.54/1.85  tff(c_3685, plain, (![A_122]: (~r2_hidden(A_122, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1457])).
% 4.54/1.85  tff(c_1149, plain, (![A_130, C_131, B_132]: (r2_hidden(A_130, k1_relat_1(k7_relat_1(C_131, B_132))) | ~r2_hidden(A_130, k1_relat_1(C_131)) | ~r2_hidden(A_130, B_132) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.54/1.85  tff(c_1178, plain, (![A_130]: (r2_hidden(A_130, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_130, k1_relat_1('#skF_3')) | ~r2_hidden(A_130, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_632, c_1149])).
% 4.54/1.85  tff(c_1199, plain, (![A_135]: (r2_hidden(A_135, k1_xboole_0) | ~r2_hidden(A_135, k1_relat_1('#skF_3')) | ~r2_hidden(A_135, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_962, c_1178])).
% 4.54/1.85  tff(c_1213, plain, (![B_2]: (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_2), k1_xboole_0) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_2), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_2))), inference(resolution, [status(thm)], [c_6, c_1199])).
% 4.54/1.85  tff(c_3929, plain, (![B_249]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_249), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_249))), inference(negUnitSimplification, [status(thm)], [c_3685, c_1213])).
% 4.54/1.85  tff(c_3937, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_4, c_3929])).
% 4.54/1.85  tff(c_3942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_633, c_633, c_3937])).
% 4.54/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.85  
% 4.54/1.85  Inference rules
% 4.54/1.85  ----------------------
% 4.54/1.85  #Ref     : 0
% 4.54/1.85  #Sup     : 895
% 4.54/1.85  #Fact    : 0
% 4.54/1.85  #Define  : 0
% 4.54/1.85  #Split   : 4
% 4.54/1.85  #Chain   : 0
% 4.54/1.85  #Close   : 0
% 4.54/1.85  
% 4.54/1.85  Ordering : KBO
% 4.54/1.85  
% 4.54/1.85  Simplification rules
% 4.54/1.85  ----------------------
% 4.54/1.85  #Subsume      : 123
% 4.54/1.85  #Demod        : 604
% 4.54/1.85  #Tautology    : 427
% 4.54/1.85  #SimpNegUnit  : 15
% 4.54/1.85  #BackRed      : 14
% 4.54/1.85  
% 4.54/1.85  #Partial instantiations: 0
% 4.54/1.85  #Strategies tried      : 1
% 4.54/1.85  
% 4.54/1.85  Timing (in seconds)
% 4.54/1.85  ----------------------
% 4.54/1.86  Preprocessing        : 0.30
% 4.54/1.86  Parsing              : 0.16
% 4.54/1.86  CNF conversion       : 0.02
% 4.54/1.86  Main loop            : 0.78
% 4.54/1.86  Inferencing          : 0.27
% 4.54/1.86  Reduction            : 0.25
% 4.54/1.86  Demodulation         : 0.18
% 4.54/1.86  BG Simplification    : 0.03
% 4.54/1.86  Subsumption          : 0.15
% 4.54/1.86  Abstraction          : 0.04
% 4.54/1.86  MUC search           : 0.00
% 4.54/1.86  Cooper               : 0.00
% 4.54/1.86  Total                : 1.12
% 4.54/1.86  Index Insertion      : 0.00
% 4.54/1.86  Index Deletion       : 0.00
% 4.54/1.86  Index Matching       : 0.00
% 4.54/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
