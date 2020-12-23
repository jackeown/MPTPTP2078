%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:46 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 729 expanded)
%              Number of leaves         :   27 ( 256 expanded)
%              Depth                    :   18
%              Number of atoms          :  116 ( 952 expanded)
%              Number of equality atoms :   85 ( 693 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_121,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_201,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_216,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_201])).

tff(c_227,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_216])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(A_16,B_17),B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_491,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,B_55)
      | ~ r2_hidden(C_56,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_543,plain,(
    ! [C_59] :
      ( ~ r2_hidden(C_59,'#skF_2')
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_491])).

tff(c_2321,plain,(
    ! [B_93] :
      ( ~ r2_hidden('#skF_1'('#skF_2',B_93),'#skF_4')
      | r1_xboole_0('#skF_2',B_93) ) ),
    inference(resolution,[status(thm)],[c_14,c_543])).

tff(c_2326,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_2321])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2333,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2326,c_4])).

tff(c_26,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2340,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2333,c_26])).

tff(c_2344,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2340])).

tff(c_281,plain,(
    ! [A_49,B_50] : k4_xboole_0(k2_xboole_0(A_49,B_50),B_50) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_294,plain,(
    ! [A_49] : k4_xboole_0(A_49,k1_xboole_0) = k2_xboole_0(A_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_20])).

tff(c_326,plain,(
    ! [A_51] : k2_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_294])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_335,plain,(
    ! [A_51] : k2_xboole_0(k1_xboole_0,A_51) = A_51 ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_2])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_153,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_138])).

tff(c_156,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_153])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_737,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k2_xboole_0(A_66,B_67),C_68) = k2_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_850,plain,(
    ! [A_69,C_70] : k2_xboole_0(A_69,k2_xboole_0(A_69,C_70)) = k2_xboole_0(A_69,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_880,plain,(
    ! [A_69,C_70] : k4_xboole_0(k2_xboole_0(A_69,C_70),k2_xboole_0(A_69,C_70)) = k4_xboole_0(A_69,k2_xboole_0(A_69,C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_22])).

tff(c_953,plain,(
    ! [A_71,C_72] : k4_xboole_0(A_71,k2_xboole_0(A_71,C_72)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_880])).

tff(c_999,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_953])).

tff(c_38,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_100,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_132,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_219,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_201])).

tff(c_228,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_1190,plain,(
    ! [A_77,B_78,C_79] : k4_xboole_0(k4_xboole_0(A_77,B_78),C_79) = k4_xboole_0(A_77,k2_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6496,plain,(
    ! [C_125] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_3',C_125)) = k4_xboole_0('#skF_5',C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_1190])).

tff(c_6591,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_6496])).

tff(c_6627,plain,(
    k4_xboole_0('#skF_5','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_6591])).

tff(c_827,plain,(
    ! [A_5,C_68] : k2_xboole_0(A_5,k2_xboole_0(A_5,C_68)) = k2_xboole_0(A_5,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_18,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1457,plain,(
    ! [A_84,A_82,B_83] : k2_xboole_0(A_84,k2_xboole_0(A_82,B_83)) = k2_xboole_0(A_82,k2_xboole_0(B_83,A_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_737])).

tff(c_3050,plain,(
    ! [A_98,A_99] : k2_xboole_0(A_98,k2_xboole_0(A_98,A_99)) = k2_xboole_0(A_99,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1457])).

tff(c_3216,plain,(
    ! [B_14,A_13] : k2_xboole_0(k4_xboole_0(B_14,A_13),A_13) = k2_xboole_0(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3050])).

tff(c_3276,plain,(
    ! [B_14,A_13] : k2_xboole_0(k4_xboole_0(B_14,A_13),A_13) = k2_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_3216])).

tff(c_6635,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k2_xboole_0('#skF_2','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6627,c_3276])).

tff(c_6654,plain,(
    k2_xboole_0('#skF_2','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_6635])).

tff(c_312,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_281])).

tff(c_919,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_850])).

tff(c_949,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2,c_919])).

tff(c_30,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_810,plain,(
    ! [C_68] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_5'),C_68) = k2_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_737])).

tff(c_2369,plain,(
    ! [C_94] : k2_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_94)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_810])).

tff(c_2463,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2369])).

tff(c_2492,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_2','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_2,c_2463])).

tff(c_2985,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2','#skF_5'),'#skF_4') = k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2492,c_312])).

tff(c_2998,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2','#skF_5'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_2985])).

tff(c_6663,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6654,c_2998])).

tff(c_6667,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_6663])).

tff(c_28,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_147,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_5151,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_147])).

tff(c_6756,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k3_xboole_0('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6667,c_5151])).

tff(c_6777,plain,(
    k3_xboole_0('#skF_5','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6667,c_6756])).

tff(c_6650,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6627,c_28])).

tff(c_6659,plain,(
    k3_xboole_0('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6650])).

tff(c_6899,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6777,c_6659])).

tff(c_303,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_281])).

tff(c_6932,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6899,c_303])).

tff(c_6953,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_22,c_6932])).

tff(c_532,plain,(
    ! [C_58] :
      ( ~ r2_hidden(C_58,'#skF_3')
      | ~ r2_hidden(C_58,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_491])).

tff(c_1871,plain,(
    ! [A_87] :
      ( ~ r2_hidden('#skF_1'(A_87,'#skF_5'),'#skF_3')
      | r1_xboole_0(A_87,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_532])).

tff(c_1876,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_1871])).

tff(c_1883,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1876,c_4])).

tff(c_6928,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6899,c_1883])).

tff(c_7054,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6928,c_26])).

tff(c_7058,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6953,c_20,c_7054])).

tff(c_7060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_7058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.49  
% 6.75/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.49  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.75/2.49  
% 6.75/2.49  %Foreground sorts:
% 6.75/2.49  
% 6.75/2.49  
% 6.75/2.49  %Background operators:
% 6.75/2.49  
% 6.75/2.49  
% 6.75/2.49  %Foreground operators:
% 6.75/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.75/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.75/2.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.75/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.75/2.49  tff('#skF_5', type, '#skF_5': $i).
% 6.75/2.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.75/2.49  tff('#skF_2', type, '#skF_2': $i).
% 6.75/2.49  tff('#skF_3', type, '#skF_3': $i).
% 6.75/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.75/2.49  tff('#skF_4', type, '#skF_4': $i).
% 6.75/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.75/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.75/2.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.75/2.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.75/2.49  
% 6.82/2.51  tff(f_76, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 6.82/2.51  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.82/2.51  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.82/2.51  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.82/2.51  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.82/2.51  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.82/2.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.82/2.51  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.82/2.51  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.82/2.51  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.82/2.51  tff(f_67, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.82/2.51  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.82/2.51  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.82/2.51  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.82/2.51  tff(c_20, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.82/2.51  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.82/2.51  tff(c_121, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.82/2.51  tff(c_133, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_121])).
% 6.82/2.51  tff(c_201, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.82/2.51  tff(c_216, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_133, c_201])).
% 6.82/2.51  tff(c_227, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_216])).
% 6.82/2.51  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.82/2.51  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.82/2.51  tff(c_14, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.82/2.51  tff(c_491, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, B_55) | ~r2_hidden(C_56, A_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.82/2.51  tff(c_543, plain, (![C_59]: (~r2_hidden(C_59, '#skF_2') | ~r2_hidden(C_59, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_491])).
% 6.82/2.51  tff(c_2321, plain, (![B_93]: (~r2_hidden('#skF_1'('#skF_2', B_93), '#skF_4') | r1_xboole_0('#skF_2', B_93))), inference(resolution, [status(thm)], [c_14, c_543])).
% 6.82/2.51  tff(c_2326, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_2321])).
% 6.82/2.51  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.82/2.51  tff(c_2333, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2326, c_4])).
% 6.82/2.51  tff(c_26, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.82/2.51  tff(c_2340, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2333, c_26])).
% 6.82/2.51  tff(c_2344, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2340])).
% 6.82/2.51  tff(c_281, plain, (![A_49, B_50]: (k4_xboole_0(k2_xboole_0(A_49, B_50), B_50)=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.82/2.51  tff(c_294, plain, (![A_49]: (k4_xboole_0(A_49, k1_xboole_0)=k2_xboole_0(A_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_281, c_20])).
% 6.82/2.51  tff(c_326, plain, (![A_51]: (k2_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_294])).
% 6.82/2.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.82/2.51  tff(c_335, plain, (![A_51]: (k2_xboole_0(k1_xboole_0, A_51)=A_51)), inference(superposition, [status(thm), theory('equality')], [c_326, c_2])).
% 6.82/2.51  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.82/2.51  tff(c_138, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.82/2.51  tff(c_153, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_138])).
% 6.82/2.51  tff(c_156, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_153])).
% 6.82/2.51  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.82/2.51  tff(c_737, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k2_xboole_0(A_66, B_67), C_68)=k2_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.82/2.51  tff(c_850, plain, (![A_69, C_70]: (k2_xboole_0(A_69, k2_xboole_0(A_69, C_70))=k2_xboole_0(A_69, C_70))), inference(superposition, [status(thm), theory('equality')], [c_8, c_737])).
% 6.82/2.51  tff(c_880, plain, (![A_69, C_70]: (k4_xboole_0(k2_xboole_0(A_69, C_70), k2_xboole_0(A_69, C_70))=k4_xboole_0(A_69, k2_xboole_0(A_69, C_70)))), inference(superposition, [status(thm), theory('equality')], [c_850, c_22])).
% 6.82/2.51  tff(c_953, plain, (![A_71, C_72]: (k4_xboole_0(A_71, k2_xboole_0(A_71, C_72))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_880])).
% 6.82/2.51  tff(c_999, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_953])).
% 6.82/2.51  tff(c_38, plain, (k2_xboole_0('#skF_2', '#skF_3')=k2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.82/2.51  tff(c_100, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2])).
% 6.82/2.51  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.82/2.51  tff(c_132, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_121])).
% 6.82/2.51  tff(c_219, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_132, c_201])).
% 6.82/2.51  tff(c_228, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_219])).
% 6.82/2.51  tff(c_1190, plain, (![A_77, B_78, C_79]: (k4_xboole_0(k4_xboole_0(A_77, B_78), C_79)=k4_xboole_0(A_77, k2_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.82/2.51  tff(c_6496, plain, (![C_125]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_3', C_125))=k4_xboole_0('#skF_5', C_125))), inference(superposition, [status(thm), theory('equality')], [c_228, c_1190])).
% 6.82/2.51  tff(c_6591, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_6496])).
% 6.82/2.51  tff(c_6627, plain, (k4_xboole_0('#skF_5', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_999, c_6591])).
% 6.82/2.51  tff(c_827, plain, (![A_5, C_68]: (k2_xboole_0(A_5, k2_xboole_0(A_5, C_68))=k2_xboole_0(A_5, C_68))), inference(superposition, [status(thm), theory('equality')], [c_8, c_737])).
% 6.82/2.51  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.82/2.51  tff(c_1457, plain, (![A_84, A_82, B_83]: (k2_xboole_0(A_84, k2_xboole_0(A_82, B_83))=k2_xboole_0(A_82, k2_xboole_0(B_83, A_84)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_737])).
% 6.82/2.51  tff(c_3050, plain, (![A_98, A_99]: (k2_xboole_0(A_98, k2_xboole_0(A_98, A_99))=k2_xboole_0(A_99, A_98))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1457])).
% 6.82/2.51  tff(c_3216, plain, (![B_14, A_13]: (k2_xboole_0(k4_xboole_0(B_14, A_13), A_13)=k2_xboole_0(A_13, k2_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3050])).
% 6.82/2.51  tff(c_3276, plain, (![B_14, A_13]: (k2_xboole_0(k4_xboole_0(B_14, A_13), A_13)=k2_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_3216])).
% 6.82/2.51  tff(c_6635, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k2_xboole_0('#skF_2', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6627, c_3276])).
% 6.82/2.51  tff(c_6654, plain, (k2_xboole_0('#skF_2', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_335, c_6635])).
% 6.82/2.51  tff(c_312, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_281])).
% 6.82/2.51  tff(c_919, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_850])).
% 6.82/2.51  tff(c_949, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2, c_919])).
% 6.82/2.51  tff(c_30, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.82/2.51  tff(c_810, plain, (![C_68]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), C_68)=k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_68)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_737])).
% 6.82/2.51  tff(c_2369, plain, (![C_94]: (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_94))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_94)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_810])).
% 6.82/2.51  tff(c_2463, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_2369])).
% 6.82/2.51  tff(c_2492, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_2', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_949, c_2, c_2463])).
% 6.82/2.51  tff(c_2985, plain, (k4_xboole_0(k2_xboole_0('#skF_2', '#skF_5'), '#skF_4')=k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2492, c_312])).
% 6.82/2.51  tff(c_2998, plain, (k4_xboole_0(k2_xboole_0('#skF_2', '#skF_5'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_2985])).
% 6.82/2.51  tff(c_6663, plain, (k4_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6654, c_2998])).
% 6.82/2.51  tff(c_6667, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2344, c_6663])).
% 6.82/2.51  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.82/2.51  tff(c_147, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k3_xboole_0(A_23, k4_xboole_0(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_138])).
% 6.82/2.51  tff(c_5151, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_147])).
% 6.82/2.51  tff(c_6756, plain, (k4_xboole_0('#skF_5', '#skF_4')=k3_xboole_0('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6667, c_5151])).
% 6.82/2.51  tff(c_6777, plain, (k3_xboole_0('#skF_5', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6667, c_6756])).
% 6.82/2.51  tff(c_6650, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6627, c_28])).
% 6.82/2.51  tff(c_6659, plain, (k3_xboole_0('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6650])).
% 6.82/2.51  tff(c_6899, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6777, c_6659])).
% 6.82/2.51  tff(c_303, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_281])).
% 6.82/2.51  tff(c_6932, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6899, c_303])).
% 6.82/2.51  tff(c_6953, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_22, c_6932])).
% 6.82/2.51  tff(c_532, plain, (![C_58]: (~r2_hidden(C_58, '#skF_3') | ~r2_hidden(C_58, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_491])).
% 6.82/2.51  tff(c_1871, plain, (![A_87]: (~r2_hidden('#skF_1'(A_87, '#skF_5'), '#skF_3') | r1_xboole_0(A_87, '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_532])).
% 6.82/2.51  tff(c_1876, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_14, c_1871])).
% 6.82/2.51  tff(c_1883, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1876, c_4])).
% 6.82/2.51  tff(c_6928, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6899, c_1883])).
% 6.82/2.51  tff(c_7054, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6928, c_26])).
% 6.82/2.51  tff(c_7058, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6953, c_20, c_7054])).
% 6.82/2.51  tff(c_7060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_7058])).
% 6.82/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.82/2.51  
% 6.82/2.51  Inference rules
% 6.82/2.51  ----------------------
% 6.82/2.51  #Ref     : 0
% 6.82/2.51  #Sup     : 1759
% 6.82/2.51  #Fact    : 0
% 6.82/2.51  #Define  : 0
% 6.82/2.51  #Split   : 0
% 6.82/2.51  #Chain   : 0
% 6.82/2.51  #Close   : 0
% 6.82/2.51  
% 6.82/2.51  Ordering : KBO
% 6.82/2.51  
% 6.82/2.51  Simplification rules
% 6.82/2.51  ----------------------
% 6.82/2.51  #Subsume      : 58
% 6.82/2.51  #Demod        : 2113
% 6.82/2.51  #Tautology    : 1009
% 6.82/2.51  #SimpNegUnit  : 1
% 6.82/2.51  #BackRed      : 40
% 6.82/2.51  
% 6.82/2.51  #Partial instantiations: 0
% 6.82/2.51  #Strategies tried      : 1
% 6.82/2.51  
% 6.82/2.51  Timing (in seconds)
% 6.82/2.51  ----------------------
% 6.91/2.52  Preprocessing        : 0.39
% 6.91/2.52  Parsing              : 0.22
% 6.91/2.52  CNF conversion       : 0.02
% 6.91/2.52  Main loop            : 1.30
% 6.91/2.52  Inferencing          : 0.31
% 6.91/2.52  Reduction            : 0.73
% 6.91/2.52  Demodulation         : 0.64
% 6.91/2.52  BG Simplification    : 0.04
% 6.91/2.52  Subsumption          : 0.16
% 6.91/2.52  Abstraction          : 0.05
% 6.91/2.52  MUC search           : 0.00
% 6.91/2.52  Cooper               : 0.00
% 6.91/2.52  Total                : 1.74
% 6.91/2.52  Index Insertion      : 0.00
% 6.91/2.52  Index Deletion       : 0.00
% 6.91/2.52  Index Matching       : 0.00
% 6.91/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
