%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:43 EST 2020

% Result     : Theorem 9.38s
% Output     : CNFRefutation 9.68s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 568 expanded)
%              Number of leaves         :   33 ( 208 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 722 expanded)
%              Number of equality atoms :   74 ( 509 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_349,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_379,plain,(
    ! [A_61,B_62] :
      ( ~ r1_xboole_0(A_61,B_62)
      | v1_xboole_0(k3_xboole_0(A_61,B_62)) ) ),
    inference(resolution,[status(thm)],[c_8,c_349])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [B_41,A_42] :
      ( ~ v1_xboole_0(B_41)
      | B_41 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_75,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_520,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_379,c_75])).

tff(c_527,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_520])).

tff(c_673,plain,(
    ! [A_75,B_76] : k2_xboole_0(k3_xboole_0(A_75,B_76),k4_xboole_0(A_75,B_76)) = A_75 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_694,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_4')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_673])).

tff(c_91,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_113,plain,(
    ! [A_46] : k2_xboole_0(k1_xboole_0,A_46) = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_16])).

tff(c_1862,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_113])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_45,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_20,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_279,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_294,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_279])).

tff(c_297,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_294])).

tff(c_726,plain,(
    ! [A_77,B_78,C_79] : k4_xboole_0(k4_xboole_0(A_77,B_78),C_79) = k4_xboole_0(A_77,k2_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_766,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k2_xboole_0(B_78,k4_xboole_0(A_77,B_78))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_726])).

tff(c_1186,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k2_xboole_0(B_90,A_89)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_766])).

tff(c_1255,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_1186])).

tff(c_14700,plain,(
    ! [C_223,A_224,B_225] : k2_xboole_0(C_223,k4_xboole_0(A_224,k2_xboole_0(B_225,C_223))) = k2_xboole_0(C_223,k4_xboole_0(A_224,B_225)) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_20])).

tff(c_15017,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_14700])).

tff(c_15150,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_16,c_15017])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_528,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_520])).

tff(c_581,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_528])).

tff(c_685,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_673])).

tff(c_2576,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_113])).

tff(c_2019,plain,(
    ! [A_107,C_108,B_109] : k2_xboole_0(k4_xboole_0(A_107,C_108),k4_xboole_0(B_109,C_108)) = k4_xboole_0(k2_xboole_0(A_107,B_109),C_108) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2134,plain,(
    ! [A_107,A_18] : k4_xboole_0(k2_xboole_0(A_107,A_18),A_18) = k2_xboole_0(k4_xboole_0(A_107,A_18),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_2019])).

tff(c_2179,plain,(
    ! [A_107,A_18] : k4_xboole_0(k2_xboole_0(A_107,A_18),A_18) = k4_xboole_0(A_107,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2134])).

tff(c_1050,plain,(
    ! [A_86,B_87,C_88] : k2_xboole_0(k2_xboole_0(A_86,B_87),C_88) = k2_xboole_0(A_86,k2_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1156,plain,(
    ! [A_86,B_87,A_1] : k2_xboole_0(A_86,k2_xboole_0(B_87,A_1)) = k2_xboole_0(A_1,k2_xboole_0(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1050])).

tff(c_3687,plain,(
    ! [A_144,A_142,B_143] : k2_xboole_0(A_144,k2_xboole_0(A_142,B_143)) = k2_xboole_0(A_142,k2_xboole_0(B_143,A_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1050])).

tff(c_404,plain,(
    ! [A_63,B_64] : k2_xboole_0(A_63,k2_xboole_0(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_439,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_404])).

tff(c_451,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_439])).

tff(c_3820,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_5','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3687,c_451])).

tff(c_4080,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1156,c_2,c_3820])).

tff(c_788,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k2_xboole_0(B_78,A_77)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_766])).

tff(c_4159,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4080,c_788])).

tff(c_15785,plain,(
    ! [A_226] : k2_xboole_0('#skF_6',k4_xboole_0(A_226,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_226,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_14700])).

tff(c_15917,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4159,c_15785])).

tff(c_15996,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15150,c_2,c_2576,c_2179,c_16,c_15917])).

tff(c_541,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_4])).

tff(c_688,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_673])).

tff(c_2507,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_113])).

tff(c_16047,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15996,c_2507])).

tff(c_691,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_3')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_673])).

tff(c_949,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_113])).

tff(c_7386,plain,(
    ! [A_183,A_184] : k4_xboole_0(k2_xboole_0(A_183,A_184),A_184) = k4_xboole_0(A_183,A_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2134])).

tff(c_7521,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_7386])).

tff(c_16022,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15996,c_15996,c_7521])).

tff(c_16066,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2179,c_949,c_16022])).

tff(c_16810,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16047,c_16066])).

tff(c_16811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_16810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.38/3.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.68/3.60  
% 9.68/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.68/3.60  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 9.68/3.60  
% 9.68/3.60  %Foreground sorts:
% 9.68/3.60  
% 9.68/3.60  
% 9.68/3.60  %Background operators:
% 9.68/3.60  
% 9.68/3.60  
% 9.68/3.60  %Foreground operators:
% 9.68/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.68/3.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.68/3.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.68/3.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.68/3.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.68/3.60  tff('#skF_5', type, '#skF_5': $i).
% 9.68/3.60  tff('#skF_6', type, '#skF_6': $i).
% 9.68/3.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.68/3.60  tff('#skF_3', type, '#skF_3': $i).
% 9.68/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.68/3.60  tff('#skF_4', type, '#skF_4': $i).
% 9.68/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.68/3.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.68/3.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.68/3.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.68/3.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.68/3.60  
% 9.68/3.62  tff(f_87, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 9.68/3.62  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.68/3.62  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.68/3.62  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.68/3.62  tff(f_78, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.68/3.62  tff(f_68, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.68/3.62  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.68/3.62  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 9.68/3.62  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.68/3.62  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.68/3.62  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.68/3.62  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.68/3.62  tff(f_60, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.68/3.62  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.68/3.62  tff(f_62, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 9.68/3.62  tff(f_66, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 9.68/3.62  tff(f_70, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 9.68/3.62  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.68/3.62  tff(c_40, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.68/3.62  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.68/3.62  tff(c_349, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.68/3.62  tff(c_379, plain, (![A_61, B_62]: (~r1_xboole_0(A_61, B_62) | v1_xboole_0(k3_xboole_0(A_61, B_62)))), inference(resolution, [status(thm)], [c_8, c_349])).
% 9.68/3.62  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.68/3.62  tff(c_72, plain, (![B_41, A_42]: (~v1_xboole_0(B_41) | B_41=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.68/3.62  tff(c_75, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_10, c_72])).
% 9.68/3.62  tff(c_520, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_xboole_0(A_69, B_70))), inference(resolution, [status(thm)], [c_379, c_75])).
% 9.68/3.62  tff(c_527, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_520])).
% 9.68/3.62  tff(c_673, plain, (![A_75, B_76]: (k2_xboole_0(k3_xboole_0(A_75, B_76), k4_xboole_0(A_75, B_76))=A_75)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.68/3.62  tff(c_694, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_4'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_527, c_673])).
% 9.68/3.62  tff(c_91, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.68/3.62  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.68/3.62  tff(c_113, plain, (![A_46]: (k2_xboole_0(k1_xboole_0, A_46)=A_46)), inference(superposition, [status(thm), theory('equality')], [c_91, c_16])).
% 9.68/3.62  tff(c_1862, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_694, c_113])).
% 9.68/3.62  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.68/3.62  tff(c_44, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.68/3.62  tff(c_45, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 9.68/3.62  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.68/3.62  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.68/3.62  tff(c_22, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.68/3.62  tff(c_279, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.68/3.62  tff(c_294, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_279])).
% 9.68/3.62  tff(c_297, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_294])).
% 9.68/3.62  tff(c_726, plain, (![A_77, B_78, C_79]: (k4_xboole_0(k4_xboole_0(A_77, B_78), C_79)=k4_xboole_0(A_77, k2_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.68/3.62  tff(c_766, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k2_xboole_0(B_78, k4_xboole_0(A_77, B_78)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_297, c_726])).
% 9.68/3.62  tff(c_1186, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k2_xboole_0(B_90, A_89))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_766])).
% 9.68/3.62  tff(c_1255, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_45, c_1186])).
% 9.68/3.62  tff(c_14700, plain, (![C_223, A_224, B_225]: (k2_xboole_0(C_223, k4_xboole_0(A_224, k2_xboole_0(B_225, C_223)))=k2_xboole_0(C_223, k4_xboole_0(A_224, B_225)))), inference(superposition, [status(thm), theory('equality')], [c_726, c_20])).
% 9.68/3.62  tff(c_15017, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1255, c_14700])).
% 9.68/3.62  tff(c_15150, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_16, c_15017])).
% 9.68/3.62  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.68/3.62  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.68/3.62  tff(c_528, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_520])).
% 9.68/3.62  tff(c_581, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_528])).
% 9.68/3.62  tff(c_685, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_581, c_673])).
% 9.68/3.62  tff(c_2576, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_685, c_113])).
% 9.68/3.62  tff(c_2019, plain, (![A_107, C_108, B_109]: (k2_xboole_0(k4_xboole_0(A_107, C_108), k4_xboole_0(B_109, C_108))=k4_xboole_0(k2_xboole_0(A_107, B_109), C_108))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.68/3.62  tff(c_2134, plain, (![A_107, A_18]: (k4_xboole_0(k2_xboole_0(A_107, A_18), A_18)=k2_xboole_0(k4_xboole_0(A_107, A_18), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_297, c_2019])).
% 9.68/3.62  tff(c_2179, plain, (![A_107, A_18]: (k4_xboole_0(k2_xboole_0(A_107, A_18), A_18)=k4_xboole_0(A_107, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2134])).
% 9.68/3.62  tff(c_1050, plain, (![A_86, B_87, C_88]: (k2_xboole_0(k2_xboole_0(A_86, B_87), C_88)=k2_xboole_0(A_86, k2_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.68/3.62  tff(c_1156, plain, (![A_86, B_87, A_1]: (k2_xboole_0(A_86, k2_xboole_0(B_87, A_1))=k2_xboole_0(A_1, k2_xboole_0(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1050])).
% 9.68/3.62  tff(c_3687, plain, (![A_144, A_142, B_143]: (k2_xboole_0(A_144, k2_xboole_0(A_142, B_143))=k2_xboole_0(A_142, k2_xboole_0(B_143, A_144)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1050])).
% 9.68/3.62  tff(c_404, plain, (![A_63, B_64]: (k2_xboole_0(A_63, k2_xboole_0(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.68/3.62  tff(c_439, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_45, c_404])).
% 9.68/3.62  tff(c_451, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_439])).
% 9.68/3.62  tff(c_3820, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_5', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3687, c_451])).
% 9.68/3.62  tff(c_4080, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1156, c_2, c_3820])).
% 9.68/3.62  tff(c_788, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k2_xboole_0(B_78, A_77))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_766])).
% 9.68/3.62  tff(c_4159, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4080, c_788])).
% 9.68/3.62  tff(c_15785, plain, (![A_226]: (k2_xboole_0('#skF_6', k4_xboole_0(A_226, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_226, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_45, c_14700])).
% 9.68/3.62  tff(c_15917, plain, (k2_xboole_0('#skF_6', k4_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4159, c_15785])).
% 9.68/3.62  tff(c_15996, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15150, c_2, c_2576, c_2179, c_16, c_15917])).
% 9.68/3.62  tff(c_541, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_527, c_4])).
% 9.68/3.62  tff(c_688, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_541, c_673])).
% 9.68/3.62  tff(c_2507, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_688, c_113])).
% 9.68/3.62  tff(c_16047, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15996, c_2507])).
% 9.68/3.62  tff(c_691, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_3'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_528, c_673])).
% 9.68/3.62  tff(c_949, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_691, c_113])).
% 9.68/3.62  tff(c_7386, plain, (![A_183, A_184]: (k4_xboole_0(k2_xboole_0(A_183, A_184), A_184)=k4_xboole_0(A_183, A_184))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2134])).
% 9.68/3.62  tff(c_7521, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_45, c_7386])).
% 9.68/3.62  tff(c_16022, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15996, c_15996, c_7521])).
% 9.68/3.62  tff(c_16066, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2179, c_949, c_16022])).
% 9.68/3.62  tff(c_16810, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16047, c_16066])).
% 9.68/3.62  tff(c_16811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_16810])).
% 9.68/3.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.68/3.62  
% 9.68/3.62  Inference rules
% 9.68/3.62  ----------------------
% 9.68/3.62  #Ref     : 0
% 9.68/3.62  #Sup     : 4314
% 9.68/3.62  #Fact    : 0
% 9.68/3.62  #Define  : 0
% 9.68/3.62  #Split   : 5
% 9.68/3.62  #Chain   : 0
% 9.68/3.62  #Close   : 0
% 9.68/3.62  
% 9.68/3.62  Ordering : KBO
% 9.68/3.62  
% 9.68/3.62  Simplification rules
% 9.68/3.62  ----------------------
% 9.68/3.62  #Subsume      : 712
% 9.68/3.62  #Demod        : 4266
% 9.68/3.62  #Tautology    : 1886
% 9.68/3.62  #SimpNegUnit  : 75
% 9.68/3.62  #BackRed      : 55
% 9.68/3.62  
% 9.68/3.62  #Partial instantiations: 0
% 9.68/3.62  #Strategies tried      : 1
% 9.68/3.62  
% 9.68/3.62  Timing (in seconds)
% 9.68/3.62  ----------------------
% 9.68/3.63  Preprocessing        : 0.31
% 9.68/3.63  Parsing              : 0.18
% 9.68/3.63  CNF conversion       : 0.02
% 9.68/3.63  Main loop            : 2.52
% 9.68/3.63  Inferencing          : 0.51
% 9.68/3.63  Reduction            : 1.47
% 9.68/3.63  Demodulation         : 1.29
% 9.68/3.63  BG Simplification    : 0.06
% 9.68/3.63  Subsumption          : 0.36
% 9.68/3.63  Abstraction          : 0.09
% 9.68/3.63  MUC search           : 0.00
% 9.68/3.63  Cooper               : 0.00
% 9.68/3.63  Total                : 2.87
% 9.68/3.63  Index Insertion      : 0.00
% 9.68/3.63  Index Deletion       : 0.00
% 9.68/3.63  Index Matching       : 0.00
% 9.68/3.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
