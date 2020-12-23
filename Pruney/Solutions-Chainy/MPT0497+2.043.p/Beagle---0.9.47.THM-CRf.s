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
% DateTime   : Thu Dec  3 09:59:45 EST 2020

% Result     : Theorem 4.98s
% Output     : CNFRefutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 284 expanded)
%              Number of leaves         :   32 ( 105 expanded)
%              Depth                    :   19
%              Number of atoms          :  162 ( 511 expanded)
%              Number of equality atoms :   41 ( 166 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_68,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_70,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_52,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_85,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_154,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1123,plain,(
    ! [A_106,B_107,C_108] :
      ( r2_hidden(A_106,B_107)
      | ~ r2_hidden(A_106,k1_relat_1(k7_relat_1(C_108,B_107)))
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1138,plain,(
    ! [A_4,C_108,B_107] :
      ( r2_hidden('#skF_1'(A_4,k1_relat_1(k7_relat_1(C_108,B_107))),B_107)
      | ~ v1_relat_1(C_108)
      | r1_xboole_0(A_4,k1_relat_1(k7_relat_1(C_108,B_107))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1123])).

tff(c_1365,plain,(
    ! [A_120,C_121,B_122] :
      ( r2_hidden(A_120,k1_relat_1(C_121))
      | ~ r2_hidden(A_120,k1_relat_1(k7_relat_1(C_121,B_122)))
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3297,plain,(
    ! [A_191,C_192,B_193] :
      ( r2_hidden('#skF_1'(A_191,k1_relat_1(k7_relat_1(C_192,B_193))),k1_relat_1(C_192))
      | ~ v1_relat_1(C_192)
      | r1_xboole_0(A_191,k1_relat_1(k7_relat_1(C_192,B_193))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1365])).

tff(c_640,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,B_76)
      | ~ r2_hidden(C_77,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_658,plain,(
    ! [C_77] :
      ( ~ r2_hidden(C_77,'#skF_3')
      | ~ r2_hidden(C_77,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_85,c_640])).

tff(c_3315,plain,(
    ! [A_191,B_193] :
      ( ~ r2_hidden('#skF_1'(A_191,k1_relat_1(k7_relat_1('#skF_4',B_193))),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | r1_xboole_0(A_191,k1_relat_1(k7_relat_1('#skF_4',B_193))) ) ),
    inference(resolution,[status(thm)],[c_3297,c_658])).

tff(c_3339,plain,(
    ! [A_194,B_195] :
      ( ~ r2_hidden('#skF_1'(A_194,k1_relat_1(k7_relat_1('#skF_4',B_195))),'#skF_3')
      | r1_xboole_0(A_194,k1_relat_1(k7_relat_1('#skF_4',B_195))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3315])).

tff(c_3351,plain,(
    ! [A_4] :
      ( ~ v1_relat_1('#skF_4')
      | r1_xboole_0(A_4,k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1138,c_3339])).

tff(c_3363,plain,(
    ! [A_196] : r1_xboole_0(A_196,k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3351])).

tff(c_18,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_188,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_220,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_224,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_220])).

tff(c_102,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r1_xboole_0(B_3,A_2)
      | ~ r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_105,plain,(
    ! [B_37,A_36] :
      ( r1_xboole_0(B_37,A_36)
      | k4_xboole_0(A_36,B_37) != A_36 ) ),
    inference(resolution,[status(thm)],[c_102,c_6])).

tff(c_225,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_220])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_230,plain,(
    ! [A_52] : k4_xboole_0(A_52,k1_xboole_0) = k3_xboole_0(A_52,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_22])).

tff(c_254,plain,(
    ! [A_53] : k3_xboole_0(A_53,A_53) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_230])).

tff(c_16,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_318,plain,(
    ! [A_55,C_56] :
      ( ~ r1_xboole_0(A_55,A_55)
      | ~ r2_hidden(C_56,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_16])).

tff(c_321,plain,(
    ! [C_56,A_36] :
      ( ~ r2_hidden(C_56,A_36)
      | k4_xboole_0(A_36,A_36) != A_36 ) ),
    inference(resolution,[status(thm)],[c_105,c_318])).

tff(c_338,plain,(
    ! [C_57,A_58] :
      ( ~ r2_hidden(C_57,A_58)
      | k1_xboole_0 != A_58 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_321])).

tff(c_361,plain,(
    ! [B_61,A_62] :
      ( k1_xboole_0 != B_61
      | r1_xboole_0(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_10,c_338])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_399,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = A_65
      | k1_xboole_0 != B_66 ) ),
    inference(resolution,[status(thm)],[c_361,c_26])).

tff(c_409,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,A_65) = k3_xboole_0(A_65,B_66)
      | k1_xboole_0 != B_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_22])).

tff(c_504,plain,(
    ! [A_65] : k3_xboole_0(A_65,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_409])).

tff(c_170,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_677,plain,(
    ! [A_80,B_81,A_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | r1_xboole_0(A_82,k3_xboole_0(A_80,B_81)) ) ),
    inference(resolution,[status(thm)],[c_10,c_170])).

tff(c_708,plain,(
    ! [A_82,A_80,B_81] :
      ( k4_xboole_0(A_82,k3_xboole_0(A_80,B_81)) = A_82
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_677,c_26])).

tff(c_1711,plain,(
    ! [A_138,B_139] : k4_xboole_0(A_138,k3_xboole_0(A_138,B_139)) = k3_xboole_0(A_138,k4_xboole_0(A_138,B_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_188])).

tff(c_2354,plain,(
    ! [A_154,B_155] :
      ( k3_xboole_0(A_154,k4_xboole_0(A_154,B_155)) = A_154
      | ~ r1_xboole_0(A_154,B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_1711])).

tff(c_2454,plain,(
    ! [A_15] :
      ( k3_xboole_0(A_15,k1_xboole_0) = A_15
      | ~ r1_xboole_0(A_15,A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_2354])).

tff(c_2478,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_xboole_0(A_15,A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_2454])).

tff(c_3400,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3363,c_2478])).

tff(c_32,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(k1_relat_1(A_23))
      | ~ v1_relat_1(A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3447,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | v1_xboole_0(k7_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3400,c_32])).

tff(c_3470,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | v1_xboole_0(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3447])).

tff(c_3987,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3470])).

tff(c_3990,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_3987])).

tff(c_3994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3990])).

tff(c_3995,plain,(
    v1_xboole_0(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3470])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4182,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3995,c_4])).

tff(c_4186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_4182])).

tff(c_4187,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4199,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4187,c_46])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4328,plain,(
    ! [A_233,B_234,C_235] :
      ( ~ r1_xboole_0(A_233,B_234)
      | ~ r2_hidden(C_235,k3_xboole_0(A_233,B_234)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4339,plain,(
    ! [A_14,C_235] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_235,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4328])).

tff(c_4343,plain,(
    ! [C_235] : ~ r2_hidden(C_235,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4339])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4947,plain,(
    ! [A_284,C_285,B_286] :
      ( r2_hidden(A_284,k1_relat_1(k7_relat_1(C_285,B_286)))
      | ~ r2_hidden(A_284,k1_relat_1(C_285))
      | ~ r2_hidden(A_284,B_286)
      | ~ v1_relat_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4959,plain,(
    ! [A_284] :
      ( r2_hidden(A_284,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_284,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_284,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4187,c_4947])).

tff(c_4964,plain,(
    ! [A_284] :
      ( r2_hidden(A_284,k1_xboole_0)
      | ~ r2_hidden(A_284,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_284,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_4959])).

tff(c_4966,plain,(
    ! [A_287] :
      ( ~ r2_hidden(A_287,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_287,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4343,c_4964])).

tff(c_5177,plain,(
    ! [B_300] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_4'),B_300),'#skF_3')
      | r1_xboole_0(k1_relat_1('#skF_4'),B_300) ) ),
    inference(resolution,[status(thm)],[c_12,c_4966])).

tff(c_5181,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5177])).

tff(c_5185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4199,c_4199,c_5181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.98/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/1.95  
% 4.98/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/1.95  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.98/1.95  
% 4.98/1.95  %Foreground sorts:
% 4.98/1.95  
% 4.98/1.95  
% 4.98/1.95  %Background operators:
% 4.98/1.95  
% 4.98/1.95  
% 4.98/1.95  %Foreground operators:
% 4.98/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.98/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.98/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.98/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.98/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.98/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.98/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.98/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.98/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.98/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.98/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.98/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.98/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.98/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.98/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.98/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.98/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.98/1.95  
% 4.98/1.97  tff(f_108, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 4.98/1.97  tff(f_82, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.98/1.97  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.98/1.97  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.98/1.97  tff(f_101, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 4.98/1.97  tff(f_68, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.98/1.97  tff(f_70, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.98/1.97  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.98/1.97  tff(f_78, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.98/1.97  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.98/1.97  tff(f_66, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.98/1.97  tff(f_90, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 4.98/1.97  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.98/1.97  tff(f_74, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.98/1.97  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.98/1.97  tff(c_52, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.98/1.97  tff(c_85, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 4.98/1.97  tff(c_46, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.98/1.97  tff(c_154, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46])).
% 4.98/1.97  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.98/1.97  tff(c_30, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.98/1.97  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.98/1.97  tff(c_10, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.98/1.97  tff(c_1123, plain, (![A_106, B_107, C_108]: (r2_hidden(A_106, B_107) | ~r2_hidden(A_106, k1_relat_1(k7_relat_1(C_108, B_107))) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.98/1.97  tff(c_1138, plain, (![A_4, C_108, B_107]: (r2_hidden('#skF_1'(A_4, k1_relat_1(k7_relat_1(C_108, B_107))), B_107) | ~v1_relat_1(C_108) | r1_xboole_0(A_4, k1_relat_1(k7_relat_1(C_108, B_107))))), inference(resolution, [status(thm)], [c_10, c_1123])).
% 4.98/1.97  tff(c_1365, plain, (![A_120, C_121, B_122]: (r2_hidden(A_120, k1_relat_1(C_121)) | ~r2_hidden(A_120, k1_relat_1(k7_relat_1(C_121, B_122))) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.98/1.97  tff(c_3297, plain, (![A_191, C_192, B_193]: (r2_hidden('#skF_1'(A_191, k1_relat_1(k7_relat_1(C_192, B_193))), k1_relat_1(C_192)) | ~v1_relat_1(C_192) | r1_xboole_0(A_191, k1_relat_1(k7_relat_1(C_192, B_193))))), inference(resolution, [status(thm)], [c_10, c_1365])).
% 4.98/1.97  tff(c_640, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, B_76) | ~r2_hidden(C_77, A_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.98/1.97  tff(c_658, plain, (![C_77]: (~r2_hidden(C_77, '#skF_3') | ~r2_hidden(C_77, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_85, c_640])).
% 4.98/1.97  tff(c_3315, plain, (![A_191, B_193]: (~r2_hidden('#skF_1'(A_191, k1_relat_1(k7_relat_1('#skF_4', B_193))), '#skF_3') | ~v1_relat_1('#skF_4') | r1_xboole_0(A_191, k1_relat_1(k7_relat_1('#skF_4', B_193))))), inference(resolution, [status(thm)], [c_3297, c_658])).
% 4.98/1.97  tff(c_3339, plain, (![A_194, B_195]: (~r2_hidden('#skF_1'(A_194, k1_relat_1(k7_relat_1('#skF_4', B_195))), '#skF_3') | r1_xboole_0(A_194, k1_relat_1(k7_relat_1('#skF_4', B_195))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3315])).
% 4.98/1.97  tff(c_3351, plain, (![A_4]: (~v1_relat_1('#skF_4') | r1_xboole_0(A_4, k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))))), inference(resolution, [status(thm)], [c_1138, c_3339])).
% 4.98/1.97  tff(c_3363, plain, (![A_196]: (r1_xboole_0(A_196, k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3351])).
% 4.98/1.97  tff(c_18, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.98/1.97  tff(c_20, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.98/1.97  tff(c_188, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.98/1.97  tff(c_220, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_188])).
% 4.98/1.97  tff(c_224, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_220])).
% 4.98/1.97  tff(c_102, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k4_xboole_0(A_36, B_37)!=A_36)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.98/1.97  tff(c_6, plain, (![B_3, A_2]: (r1_xboole_0(B_3, A_2) | ~r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.98/1.97  tff(c_105, plain, (![B_37, A_36]: (r1_xboole_0(B_37, A_36) | k4_xboole_0(A_36, B_37)!=A_36)), inference(resolution, [status(thm)], [c_102, c_6])).
% 4.98/1.97  tff(c_225, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_220])).
% 4.98/1.97  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.98/1.97  tff(c_230, plain, (![A_52]: (k4_xboole_0(A_52, k1_xboole_0)=k3_xboole_0(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_225, c_22])).
% 4.98/1.97  tff(c_254, plain, (![A_53]: (k3_xboole_0(A_53, A_53)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_230])).
% 4.98/1.97  tff(c_16, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.98/1.97  tff(c_318, plain, (![A_55, C_56]: (~r1_xboole_0(A_55, A_55) | ~r2_hidden(C_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_254, c_16])).
% 4.98/1.97  tff(c_321, plain, (![C_56, A_36]: (~r2_hidden(C_56, A_36) | k4_xboole_0(A_36, A_36)!=A_36)), inference(resolution, [status(thm)], [c_105, c_318])).
% 4.98/1.97  tff(c_338, plain, (![C_57, A_58]: (~r2_hidden(C_57, A_58) | k1_xboole_0!=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_321])).
% 4.98/1.97  tff(c_361, plain, (![B_61, A_62]: (k1_xboole_0!=B_61 | r1_xboole_0(A_62, B_61))), inference(resolution, [status(thm)], [c_10, c_338])).
% 4.98/1.97  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.98/1.97  tff(c_399, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=A_65 | k1_xboole_0!=B_66)), inference(resolution, [status(thm)], [c_361, c_26])).
% 4.98/1.97  tff(c_409, plain, (![A_65, B_66]: (k4_xboole_0(A_65, A_65)=k3_xboole_0(A_65, B_66) | k1_xboole_0!=B_66)), inference(superposition, [status(thm), theory('equality')], [c_399, c_22])).
% 4.98/1.97  tff(c_504, plain, (![A_65]: (k3_xboole_0(A_65, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_409])).
% 4.98/1.97  tff(c_170, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.98/1.97  tff(c_677, plain, (![A_80, B_81, A_82]: (~r1_xboole_0(A_80, B_81) | r1_xboole_0(A_82, k3_xboole_0(A_80, B_81)))), inference(resolution, [status(thm)], [c_10, c_170])).
% 4.98/1.97  tff(c_708, plain, (![A_82, A_80, B_81]: (k4_xboole_0(A_82, k3_xboole_0(A_80, B_81))=A_82 | ~r1_xboole_0(A_80, B_81))), inference(resolution, [status(thm)], [c_677, c_26])).
% 4.98/1.97  tff(c_1711, plain, (![A_138, B_139]: (k4_xboole_0(A_138, k3_xboole_0(A_138, B_139))=k3_xboole_0(A_138, k4_xboole_0(A_138, B_139)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_188])).
% 4.98/1.97  tff(c_2354, plain, (![A_154, B_155]: (k3_xboole_0(A_154, k4_xboole_0(A_154, B_155))=A_154 | ~r1_xboole_0(A_154, B_155))), inference(superposition, [status(thm), theory('equality')], [c_708, c_1711])).
% 4.98/1.97  tff(c_2454, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=A_15 | ~r1_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_224, c_2354])).
% 4.98/1.97  tff(c_2478, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_xboole_0(A_15, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_504, c_2454])).
% 4.98/1.97  tff(c_3400, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3363, c_2478])).
% 4.98/1.97  tff(c_32, plain, (![A_23]: (~v1_xboole_0(k1_relat_1(A_23)) | ~v1_relat_1(A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.98/1.97  tff(c_3447, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | v1_xboole_0(k7_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3400, c_32])).
% 4.98/1.97  tff(c_3470, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | v1_xboole_0(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3447])).
% 4.98/1.97  tff(c_3987, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3470])).
% 4.98/1.97  tff(c_3990, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_3987])).
% 4.98/1.97  tff(c_3994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_3990])).
% 4.98/1.97  tff(c_3995, plain, (v1_xboole_0(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_3470])).
% 4.98/1.97  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.98/1.97  tff(c_4182, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3995, c_4])).
% 4.98/1.97  tff(c_4186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_4182])).
% 4.98/1.97  tff(c_4187, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 4.98/1.97  tff(c_4199, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4187, c_46])).
% 4.98/1.97  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.98/1.97  tff(c_24, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.98/1.97  tff(c_4328, plain, (![A_233, B_234, C_235]: (~r1_xboole_0(A_233, B_234) | ~r2_hidden(C_235, k3_xboole_0(A_233, B_234)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.98/1.97  tff(c_4339, plain, (![A_14, C_235]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_235, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4328])).
% 4.98/1.97  tff(c_4343, plain, (![C_235]: (~r2_hidden(C_235, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4339])).
% 4.98/1.97  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.98/1.97  tff(c_4947, plain, (![A_284, C_285, B_286]: (r2_hidden(A_284, k1_relat_1(k7_relat_1(C_285, B_286))) | ~r2_hidden(A_284, k1_relat_1(C_285)) | ~r2_hidden(A_284, B_286) | ~v1_relat_1(C_285))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.98/1.97  tff(c_4959, plain, (![A_284]: (r2_hidden(A_284, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_284, k1_relat_1('#skF_4')) | ~r2_hidden(A_284, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4187, c_4947])).
% 4.98/1.97  tff(c_4964, plain, (![A_284]: (r2_hidden(A_284, k1_xboole_0) | ~r2_hidden(A_284, k1_relat_1('#skF_4')) | ~r2_hidden(A_284, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_4959])).
% 4.98/1.97  tff(c_4966, plain, (![A_287]: (~r2_hidden(A_287, k1_relat_1('#skF_4')) | ~r2_hidden(A_287, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_4343, c_4964])).
% 4.98/1.97  tff(c_5177, plain, (![B_300]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_4'), B_300), '#skF_3') | r1_xboole_0(k1_relat_1('#skF_4'), B_300))), inference(resolution, [status(thm)], [c_12, c_4966])).
% 4.98/1.97  tff(c_5181, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_10, c_5177])).
% 4.98/1.97  tff(c_5185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4199, c_4199, c_5181])).
% 4.98/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/1.97  
% 4.98/1.97  Inference rules
% 4.98/1.97  ----------------------
% 4.98/1.97  #Ref     : 0
% 4.98/1.97  #Sup     : 1244
% 4.98/1.97  #Fact    : 0
% 4.98/1.97  #Define  : 0
% 4.98/1.97  #Split   : 4
% 4.98/1.97  #Chain   : 0
% 4.98/1.97  #Close   : 0
% 4.98/1.97  
% 4.98/1.97  Ordering : KBO
% 4.98/1.97  
% 4.98/1.97  Simplification rules
% 4.98/1.97  ----------------------
% 4.98/1.97  #Subsume      : 309
% 4.98/1.97  #Demod        : 462
% 4.98/1.97  #Tautology    : 629
% 4.98/1.97  #SimpNegUnit  : 30
% 4.98/1.97  #BackRed      : 1
% 4.98/1.97  
% 4.98/1.97  #Partial instantiations: 0
% 4.98/1.97  #Strategies tried      : 1
% 4.98/1.97  
% 4.98/1.97  Timing (in seconds)
% 4.98/1.97  ----------------------
% 4.98/1.97  Preprocessing        : 0.29
% 4.98/1.97  Parsing              : 0.17
% 4.98/1.97  CNF conversion       : 0.02
% 4.98/1.97  Main loop            : 0.87
% 4.98/1.97  Inferencing          : 0.32
% 4.98/1.97  Reduction            : 0.27
% 4.98/1.97  Demodulation         : 0.19
% 4.98/1.97  BG Simplification    : 0.03
% 4.98/1.97  Subsumption          : 0.19
% 4.98/1.97  Abstraction          : 0.04
% 4.98/1.97  MUC search           : 0.00
% 4.98/1.97  Cooper               : 0.00
% 4.98/1.97  Total                : 1.20
% 4.98/1.97  Index Insertion      : 0.00
% 4.98/1.97  Index Deletion       : 0.00
% 4.98/1.97  Index Matching       : 0.00
% 4.98/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
