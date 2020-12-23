%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:49 EST 2020

% Result     : Theorem 27.77s
% Output     : CNFRefutation 27.97s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 637 expanded)
%              Number of leaves         :   38 ( 225 expanded)
%              Depth                    :   20
%              Number of atoms          :  231 (1138 expanded)
%              Number of equality atoms :   47 ( 245 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_115,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_70,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | r1_tarski(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_199,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_76])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_203,plain,(
    k3_xboole_0(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4','#skF_5')) = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_199,c_24])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1423,plain,(
    ! [A_146,B_147] :
      ( k4_xboole_0(A_146,B_147) = k3_subset_1(A_146,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1440,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1423])).

tff(c_94,plain,(
    ! [B_66,A_67] : k3_xboole_0(B_66,A_67) = k3_xboole_0(A_67,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [B_66,A_67] : r1_tarski(k3_xboole_0(B_66,A_67),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_20])).

tff(c_32,plain,(
    ! [A_29,B_30] : r1_xboole_0(k4_xboole_0(A_29,B_30),B_30) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    ! [B_62,A_63] :
      ( r1_xboole_0(B_62,A_63)
      | ~ r1_xboole_0(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [B_30,A_29] : r1_xboole_0(B_30,k4_xboole_0(A_29,B_30)) ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(A_36,k4_xboole_0(B_37,C_38))
      | ~ r1_xboole_0(A_36,C_38)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_339,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5115,plain,(
    ! [A_304,B_305] :
      ( k4_xboole_0(A_304,B_305) = A_304
      | ~ r1_tarski(A_304,k4_xboole_0(A_304,B_305)) ) ),
    inference(resolution,[status(thm)],[c_26,c_339])).

tff(c_5119,plain,(
    ! [B_37,C_38] :
      ( k4_xboole_0(B_37,C_38) = B_37
      | ~ r1_xboole_0(B_37,C_38)
      | ~ r1_tarski(B_37,B_37) ) ),
    inference(resolution,[status(thm)],[c_38,c_5115])).

tff(c_5139,plain,(
    ! [B_306,C_307] :
      ( k4_xboole_0(B_306,C_307) = B_306
      | ~ r1_xboole_0(B_306,C_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5119])).

tff(c_5384,plain,(
    ! [B_309,A_310] : k4_xboole_0(B_309,k4_xboole_0(A_310,B_309)) = B_309 ),
    inference(resolution,[status(thm)],[c_87,c_5139])).

tff(c_515,plain,(
    ! [A_102,C_103,B_104] :
      ( r1_xboole_0(A_102,k4_xboole_0(C_103,B_104))
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_521,plain,(
    ! [C_103,B_104,A_102] :
      ( r1_xboole_0(k4_xboole_0(C_103,B_104),A_102)
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(resolution,[status(thm)],[c_515,c_10])).

tff(c_20548,plain,(
    ! [B_549,A_550,A_551] :
      ( r1_xboole_0(B_549,A_550)
      | ~ r1_tarski(A_550,k4_xboole_0(A_551,B_549)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5384,c_521])).

tff(c_20899,plain,(
    ! [B_554,B_555,A_556] : r1_xboole_0(B_554,k3_xboole_0(B_555,k4_xboole_0(A_556,B_554))) ),
    inference(resolution,[status(thm)],[c_109,c_20548])).

tff(c_21225,plain,(
    ! [B_563] : r1_xboole_0('#skF_5',k3_xboole_0(B_563,k3_subset_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_20899])).

tff(c_21264,plain,(
    r1_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_21225])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1439,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1423])).

tff(c_1025,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_tarski(A_128,k2_xboole_0(B_129,C_130))
      | ~ r1_tarski(k4_xboole_0(A_128,B_129),C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1060,plain,(
    ! [A_128,B_129] : r1_tarski(A_128,k2_xboole_0(B_129,k4_xboole_0(A_128,B_129))) ),
    inference(resolution,[status(thm)],[c_16,c_1025])).

tff(c_1445,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6',k3_subset_1('#skF_4','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1439,c_1060])).

tff(c_144,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_164,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(resolution,[status(thm)],[c_16,c_144])).

tff(c_64,plain,(
    ! [A_50] : ~ v1_xboole_0(k1_zfmisc_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    ! [C_43,A_39] :
      ( r2_hidden(C_43,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_43,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_392,plain,(
    ! [B_95,A_96] :
      ( m1_subset_1(B_95,A_96)
      | ~ r2_hidden(B_95,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_401,plain,(
    ! [C_43,A_39] :
      ( m1_subset_1(C_43,k1_zfmisc_1(A_39))
      | v1_xboole_0(k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_43,A_39) ) ),
    inference(resolution,[status(thm)],[c_42,c_392])).

tff(c_406,plain,(
    ! [C_43,A_39] :
      ( m1_subset_1(C_43,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_43,A_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_401])).

tff(c_22337,plain,(
    ! [A_576,C_577] :
      ( k4_xboole_0(A_576,C_577) = k3_subset_1(A_576,C_577)
      | ~ r1_tarski(C_577,A_576) ) ),
    inference(resolution,[status(thm)],[c_406,c_1423])).

tff(c_22886,plain,(
    ! [B_578] : k4_xboole_0(B_578,B_578) = k3_subset_1(B_578,B_578) ),
    inference(resolution,[status(thm)],[c_16,c_22337])).

tff(c_18,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [A_14,B_15] : k3_xboole_0(k3_xboole_0(A_14,B_15),A_14) = k3_xboole_0(A_14,B_15) ),
    inference(resolution,[status(thm)],[c_20,c_144])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_416,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3493,plain,(
    ! [B_234,A_235] : k5_xboole_0(B_234,k3_xboole_0(A_235,B_234)) = k4_xboole_0(B_234,A_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_416])).

tff(c_3521,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_3493])).

tff(c_7041,plain,(
    ! [A_358,B_359] : k4_xboole_0(A_358,k3_xboole_0(A_358,B_359)) = k4_xboole_0(A_358,B_359) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3521])).

tff(c_7190,plain,(
    ! [A_358,B_359] : r1_xboole_0(k4_xboole_0(A_358,B_359),k3_xboole_0(A_358,B_359)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7041,c_32])).

tff(c_22983,plain,(
    ! [B_578] : r1_xboole_0(k3_subset_1(B_578,B_578),k3_xboole_0(B_578,B_578)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22886,c_7190])).

tff(c_23144,plain,(
    ! [B_578] : r1_xboole_0(k3_subset_1(B_578,B_578),B_578) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_22983])).

tff(c_22873,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k3_subset_1(B_11,B_11) ),
    inference(resolution,[status(thm)],[c_16,c_22337])).

tff(c_440,plain,(
    ! [B_11] : k5_xboole_0(B_11,B_11) = k4_xboole_0(B_11,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_416])).

tff(c_22885,plain,(
    ! [B_11] : k5_xboole_0(B_11,B_11) = k3_subset_1(B_11,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22873,c_440])).

tff(c_223,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    ! [C_43,A_39] :
      ( r1_tarski(C_43,A_39)
      | ~ r2_hidden(C_43,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_227,plain,(
    ! [B_83,A_39] :
      ( r1_tarski(B_83,A_39)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_39))
      | v1_xboole_0(k1_zfmisc_1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_223,c_40])).

tff(c_231,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(B_85,A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_227])).

tff(c_243,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_231])).

tff(c_259,plain,(
    k3_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_243,c_24])).

tff(c_434,plain,(
    k5_xboole_0('#skF_6','#skF_6') = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_416])).

tff(c_23525,plain,(
    k4_xboole_0('#skF_6','#skF_4') = k3_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22885,c_434])).

tff(c_1061,plain,(
    ! [A_131,B_132] : r1_tarski(A_131,k2_xboole_0(B_132,A_131)) ),
    inference(resolution,[status(thm)],[c_26,c_1025])).

tff(c_1076,plain,(
    ! [A_131,B_132] : k3_xboole_0(A_131,k2_xboole_0(B_132,A_131)) = A_131 ),
    inference(resolution,[status(thm)],[c_1061,c_24])).

tff(c_555,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_tarski(A_105,C_106)
      | ~ r1_tarski(B_107,C_106)
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_892,plain,(
    ! [A_122,A_123,B_124] :
      ( r1_tarski(A_122,A_123)
      | ~ r1_tarski(A_122,k3_xboole_0(A_123,B_124)) ) ),
    inference(resolution,[status(thm)],[c_20,c_555])).

tff(c_1569,plain,(
    ! [A_151,B_152,B_153] : r1_tarski(k4_xboole_0(k3_xboole_0(A_151,B_152),B_153),A_151) ),
    inference(resolution,[status(thm)],[c_26,c_892])).

tff(c_1720,plain,(
    ! [B_157,A_158,B_159] : r1_tarski(k4_xboole_0(k3_xboole_0(B_157,A_158),B_159),A_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1569])).

tff(c_1751,plain,(
    ! [A_131,B_159,B_132] : r1_tarski(k4_xboole_0(A_131,B_159),k2_xboole_0(B_132,A_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_1720])).

tff(c_26980,plain,(
    ! [B_618] : r1_tarski(k3_subset_1('#skF_6','#skF_6'),k2_xboole_0(B_618,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23525,c_1751])).

tff(c_30,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,B_27)
      | ~ r1_xboole_0(A_26,C_28)
      | ~ r1_tarski(A_26,k2_xboole_0(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26990,plain,(
    ! [B_618] :
      ( r1_tarski(k3_subset_1('#skF_6','#skF_6'),B_618)
      | ~ r1_xboole_0(k3_subset_1('#skF_6','#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26980,c_30])).

tff(c_27120,plain,(
    ! [B_621] : r1_tarski(k3_subset_1('#skF_6','#skF_6'),B_621) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23144,c_26990])).

tff(c_5462,plain,(
    ! [B_309,A_102,A_310] :
      ( r1_xboole_0(B_309,A_102)
      | ~ r1_tarski(A_102,k4_xboole_0(A_310,B_309)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5384,c_521])).

tff(c_27210,plain,(
    ! [B_309] : r1_xboole_0(B_309,k3_subset_1('#skF_6','#skF_6')) ),
    inference(resolution,[status(thm)],[c_27120,c_5462])).

tff(c_27243,plain,(
    ! [B_622] : r1_xboole_0(B_622,k3_subset_1('#skF_6','#skF_6')) ),
    inference(resolution,[status(thm)],[c_27120,c_5462])).

tff(c_5134,plain,(
    ! [B_37,C_38] :
      ( k4_xboole_0(B_37,C_38) = B_37
      | ~ r1_xboole_0(B_37,C_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5119])).

tff(c_27341,plain,(
    ! [B_626] : k4_xboole_0(B_626,k3_subset_1('#skF_6','#skF_6')) = B_626 ),
    inference(resolution,[status(thm)],[c_27243,c_5134])).

tff(c_244,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_231])).

tff(c_1522,plain,(
    ! [A_148,B_149,C_150] :
      ( r1_tarski(A_148,k4_xboole_0(B_149,C_150))
      | ~ r1_xboole_0(A_148,C_150)
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(A_16,C_18)
      | ~ r1_tarski(B_17,C_18)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9321,plain,(
    ! [A_405,B_406,C_407,A_408] :
      ( r1_tarski(A_405,k4_xboole_0(B_406,C_407))
      | ~ r1_tarski(A_405,A_408)
      | ~ r1_xboole_0(A_408,C_407)
      | ~ r1_tarski(A_408,B_406) ) ),
    inference(resolution,[status(thm)],[c_1522,c_22])).

tff(c_9623,plain,(
    ! [B_406,C_407] :
      ( r1_tarski('#skF_5',k4_xboole_0(B_406,C_407))
      | ~ r1_xboole_0('#skF_4',C_407)
      | ~ r1_tarski('#skF_4',B_406) ) ),
    inference(resolution,[status(thm)],[c_244,c_9321])).

tff(c_27453,plain,(
    ! [B_626] :
      ( r1_tarski('#skF_5',B_626)
      | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_6','#skF_6'))
      | ~ r1_tarski('#skF_4',B_626) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27341,c_9623])).

tff(c_27662,plain,(
    ! [B_626] :
      ( r1_tarski('#skF_5',B_626)
      | ~ r1_tarski('#skF_4',B_626) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27210,c_27453])).

tff(c_28339,plain,(
    ! [B_637,B_638] : r1_tarski(k3_subset_1(B_637,B_637),k2_xboole_0(B_638,B_637)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22886,c_1751])).

tff(c_28349,plain,(
    ! [B_637,B_638] :
      ( r1_tarski(k3_subset_1(B_637,B_637),B_638)
      | ~ r1_xboole_0(k3_subset_1(B_637,B_637),B_637) ) ),
    inference(resolution,[status(thm)],[c_28339,c_30])).

tff(c_28417,plain,(
    ! [B_642,B_643] : r1_tarski(k3_subset_1(B_642,B_642),B_643) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23144,c_28349])).

tff(c_28505,plain,(
    ! [B_309,B_642] : r1_xboole_0(B_309,k3_subset_1(B_642,B_642)) ),
    inference(resolution,[status(thm)],[c_28417,c_5462])).

tff(c_28657,plain,(
    ! [B_647,B_648] : r1_xboole_0(B_647,k3_subset_1(B_648,B_648)) ),
    inference(resolution,[status(thm)],[c_28417,c_5462])).

tff(c_28682,plain,(
    ! [B_647,B_648] : k4_xboole_0(B_647,k3_subset_1(B_648,B_648)) = B_647 ),
    inference(resolution,[status(thm)],[c_28657,c_5134])).

tff(c_8592,plain,(
    ! [A_391,B_392,C_393] :
      ( k3_xboole_0(A_391,k4_xboole_0(B_392,C_393)) = A_391
      | ~ r1_xboole_0(A_391,C_393)
      | ~ r1_tarski(A_391,B_392) ) ),
    inference(resolution,[status(thm)],[c_1522,c_24])).

tff(c_39002,plain,(
    ! [B_821,C_822,B_823] :
      ( k3_xboole_0(k4_xboole_0(B_821,C_822),B_823) = B_823
      | ~ r1_xboole_0(B_823,C_822)
      | ~ r1_tarski(B_823,B_821) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8592])).

tff(c_39375,plain,(
    ! [B_647,B_823,B_648] :
      ( k3_xboole_0(B_647,B_823) = B_823
      | ~ r1_xboole_0(B_823,k3_subset_1(B_648,B_648))
      | ~ r1_tarski(B_823,B_647) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28682,c_39002])).

tff(c_60083,plain,(
    ! [B_1061,B_1062] :
      ( k3_xboole_0(B_1061,B_1062) = B_1062
      | ~ r1_tarski(B_1062,B_1061) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28505,c_39375])).

tff(c_65943,plain,(
    ! [B_1145] :
      ( k3_xboole_0(B_1145,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_4',B_1145) ) ),
    inference(resolution,[status(thm)],[c_27662,c_60083])).

tff(c_66148,plain,(
    k3_xboole_0(k2_xboole_0('#skF_6',k3_subset_1('#skF_4','#skF_6')),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1445,c_65943])).

tff(c_75602,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_6',k3_subset_1('#skF_4','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_66148,c_20])).

tff(c_75764,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_75602,c_30])).

tff(c_75789,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21264,c_75764])).

tff(c_75791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_75789])).

tff(c_75793,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_76395,plain,(
    ! [A_1311,B_1312] :
      ( k4_xboole_0(A_1311,B_1312) = k3_subset_1(A_1311,B_1312)
      | ~ m1_subset_1(B_1312,k1_zfmisc_1(A_1311)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_76411,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_76395])).

tff(c_75990,plain,(
    ! [A_1285,C_1286,B_1287] :
      ( r1_xboole_0(A_1285,k4_xboole_0(C_1286,B_1287))
      | ~ r1_tarski(A_1285,B_1287) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77584,plain,(
    ! [C_1362,B_1363,A_1364] :
      ( r1_xboole_0(k4_xboole_0(C_1362,B_1363),A_1364)
      | ~ r1_tarski(A_1364,B_1363) ) ),
    inference(resolution,[status(thm)],[c_75990,c_10])).

tff(c_77604,plain,(
    ! [A_1364] :
      ( r1_xboole_0(k3_subset_1('#skF_4','#skF_6'),A_1364)
      | ~ r1_tarski(A_1364,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76411,c_77584])).

tff(c_76423,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_76411,c_26])).

tff(c_76412,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_76395])).

tff(c_76692,plain,(
    ! [A_1324,B_1325,C_1326] :
      ( r1_tarski(A_1324,k4_xboole_0(B_1325,C_1326))
      | ~ r1_xboole_0(A_1324,C_1326)
      | ~ r1_tarski(A_1324,B_1325) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82658,plain,(
    ! [A_1527] :
      ( r1_tarski(A_1527,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_xboole_0(A_1527,'#skF_5')
      | ~ r1_tarski(A_1527,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76412,c_76692])).

tff(c_75792,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_82698,plain,
    ( ~ r1_xboole_0(k3_subset_1('#skF_4','#skF_6'),'#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_82658,c_75792])).

tff(c_82716,plain,(
    ~ r1_xboole_0(k3_subset_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76423,c_82698])).

tff(c_82719,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_77604,c_82716])).

tff(c_82723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75793,c_82719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.77/18.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.91/18.98  
% 27.91/18.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.91/18.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 27.91/18.98  
% 27.91/18.98  %Foreground sorts:
% 27.91/18.98  
% 27.91/18.98  
% 27.91/18.98  %Background operators:
% 27.91/18.98  
% 27.91/18.98  
% 27.91/18.98  %Foreground operators:
% 27.91/18.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.91/18.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.91/18.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.91/18.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 27.91/18.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.91/18.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.91/18.98  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 27.91/18.98  tff('#skF_5', type, '#skF_5': $i).
% 27.91/18.98  tff('#skF_6', type, '#skF_6': $i).
% 27.91/18.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 27.91/18.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.91/18.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.91/18.98  tff('#skF_4', type, '#skF_4': $i).
% 27.91/18.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.91/18.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.91/18.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.91/18.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.91/18.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.91/18.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.91/18.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.91/18.98  
% 27.97/19.01  tff(f_125, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 27.97/19.01  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 27.97/19.01  tff(f_112, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 27.97/19.01  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.97/19.01  tff(f_48, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 27.97/19.01  tff(f_72, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 27.97/19.01  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 27.97/19.01  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.97/19.01  tff(f_84, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 27.97/19.01  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 27.97/19.01  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 27.97/19.01  tff(f_64, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 27.97/19.01  tff(f_115, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 27.97/19.01  tff(f_91, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 27.97/19.01  tff(f_108, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 27.97/19.01  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 27.97/19.01  tff(f_54, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 27.97/19.01  tff(f_70, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 27.97/19.01  tff(c_70, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 27.97/19.01  tff(c_88, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_70])).
% 27.97/19.01  tff(c_76, plain, (r1_tarski('#skF_5', '#skF_6') | r1_tarski(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 27.97/19.01  tff(c_199, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_88, c_76])).
% 27.97/19.01  tff(c_24, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.97/19.01  tff(c_203, plain, (k3_xboole_0(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', '#skF_5'))=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_199, c_24])).
% 27.97/19.01  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 27.97/19.01  tff(c_1423, plain, (![A_146, B_147]: (k4_xboole_0(A_146, B_147)=k3_subset_1(A_146, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 27.97/19.01  tff(c_1440, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_1423])).
% 27.97/19.01  tff(c_94, plain, (![B_66, A_67]: (k3_xboole_0(B_66, A_67)=k3_xboole_0(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.97/19.01  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 27.97/19.01  tff(c_109, plain, (![B_66, A_67]: (r1_tarski(k3_xboole_0(B_66, A_67), A_67))), inference(superposition, [status(thm), theory('equality')], [c_94, c_20])).
% 27.97/19.01  tff(c_32, plain, (![A_29, B_30]: (r1_xboole_0(k4_xboole_0(A_29, B_30), B_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 27.97/19.01  tff(c_84, plain, (![B_62, A_63]: (r1_xboole_0(B_62, A_63) | ~r1_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.97/19.01  tff(c_87, plain, (![B_30, A_29]: (r1_xboole_0(B_30, k4_xboole_0(A_29, B_30)))), inference(resolution, [status(thm)], [c_32, c_84])).
% 27.97/19.01  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.97/19.01  tff(c_38, plain, (![A_36, B_37, C_38]: (r1_tarski(A_36, k4_xboole_0(B_37, C_38)) | ~r1_xboole_0(A_36, C_38) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.97/19.01  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 27.97/19.01  tff(c_339, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.97/19.01  tff(c_5115, plain, (![A_304, B_305]: (k4_xboole_0(A_304, B_305)=A_304 | ~r1_tarski(A_304, k4_xboole_0(A_304, B_305)))), inference(resolution, [status(thm)], [c_26, c_339])).
% 27.97/19.01  tff(c_5119, plain, (![B_37, C_38]: (k4_xboole_0(B_37, C_38)=B_37 | ~r1_xboole_0(B_37, C_38) | ~r1_tarski(B_37, B_37))), inference(resolution, [status(thm)], [c_38, c_5115])).
% 27.97/19.01  tff(c_5139, plain, (![B_306, C_307]: (k4_xboole_0(B_306, C_307)=B_306 | ~r1_xboole_0(B_306, C_307))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5119])).
% 27.97/19.01  tff(c_5384, plain, (![B_309, A_310]: (k4_xboole_0(B_309, k4_xboole_0(A_310, B_309))=B_309)), inference(resolution, [status(thm)], [c_87, c_5139])).
% 27.97/19.01  tff(c_515, plain, (![A_102, C_103, B_104]: (r1_xboole_0(A_102, k4_xboole_0(C_103, B_104)) | ~r1_tarski(A_102, B_104))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.97/19.01  tff(c_10, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.97/19.01  tff(c_521, plain, (![C_103, B_104, A_102]: (r1_xboole_0(k4_xboole_0(C_103, B_104), A_102) | ~r1_tarski(A_102, B_104))), inference(resolution, [status(thm)], [c_515, c_10])).
% 27.97/19.01  tff(c_20548, plain, (![B_549, A_550, A_551]: (r1_xboole_0(B_549, A_550) | ~r1_tarski(A_550, k4_xboole_0(A_551, B_549)))), inference(superposition, [status(thm), theory('equality')], [c_5384, c_521])).
% 27.97/19.01  tff(c_20899, plain, (![B_554, B_555, A_556]: (r1_xboole_0(B_554, k3_xboole_0(B_555, k4_xboole_0(A_556, B_554))))), inference(resolution, [status(thm)], [c_109, c_20548])).
% 27.97/19.01  tff(c_21225, plain, (![B_563]: (r1_xboole_0('#skF_5', k3_xboole_0(B_563, k3_subset_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_1440, c_20899])).
% 27.97/19.01  tff(c_21264, plain, (r1_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_21225])).
% 27.97/19.01  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 27.97/19.01  tff(c_1439, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_1423])).
% 27.97/19.01  tff(c_1025, plain, (![A_128, B_129, C_130]: (r1_tarski(A_128, k2_xboole_0(B_129, C_130)) | ~r1_tarski(k4_xboole_0(A_128, B_129), C_130))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.97/19.01  tff(c_1060, plain, (![A_128, B_129]: (r1_tarski(A_128, k2_xboole_0(B_129, k4_xboole_0(A_128, B_129))))), inference(resolution, [status(thm)], [c_16, c_1025])).
% 27.97/19.01  tff(c_1445, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1439, c_1060])).
% 27.97/19.01  tff(c_144, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.97/19.01  tff(c_164, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(resolution, [status(thm)], [c_16, c_144])).
% 27.97/19.01  tff(c_64, plain, (![A_50]: (~v1_xboole_0(k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 27.97/19.01  tff(c_42, plain, (![C_43, A_39]: (r2_hidden(C_43, k1_zfmisc_1(A_39)) | ~r1_tarski(C_43, A_39))), inference(cnfTransformation, [status(thm)], [f_91])).
% 27.97/19.01  tff(c_392, plain, (![B_95, A_96]: (m1_subset_1(B_95, A_96) | ~r2_hidden(B_95, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_108])).
% 27.97/19.01  tff(c_401, plain, (![C_43, A_39]: (m1_subset_1(C_43, k1_zfmisc_1(A_39)) | v1_xboole_0(k1_zfmisc_1(A_39)) | ~r1_tarski(C_43, A_39))), inference(resolution, [status(thm)], [c_42, c_392])).
% 27.97/19.01  tff(c_406, plain, (![C_43, A_39]: (m1_subset_1(C_43, k1_zfmisc_1(A_39)) | ~r1_tarski(C_43, A_39))), inference(negUnitSimplification, [status(thm)], [c_64, c_401])).
% 27.97/19.01  tff(c_22337, plain, (![A_576, C_577]: (k4_xboole_0(A_576, C_577)=k3_subset_1(A_576, C_577) | ~r1_tarski(C_577, A_576))), inference(resolution, [status(thm)], [c_406, c_1423])).
% 27.97/19.01  tff(c_22886, plain, (![B_578]: (k4_xboole_0(B_578, B_578)=k3_subset_1(B_578, B_578))), inference(resolution, [status(thm)], [c_16, c_22337])).
% 27.97/19.01  tff(c_18, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 27.97/19.01  tff(c_161, plain, (![A_14, B_15]: (k3_xboole_0(k3_xboole_0(A_14, B_15), A_14)=k3_xboole_0(A_14, B_15))), inference(resolution, [status(thm)], [c_20, c_144])).
% 27.97/19.01  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.97/19.01  tff(c_416, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_46])).
% 27.97/19.01  tff(c_3493, plain, (![B_234, A_235]: (k5_xboole_0(B_234, k3_xboole_0(A_235, B_234))=k4_xboole_0(B_234, A_235))), inference(superposition, [status(thm), theory('equality')], [c_2, c_416])).
% 27.97/19.01  tff(c_3521, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_3493])).
% 27.97/19.01  tff(c_7041, plain, (![A_358, B_359]: (k4_xboole_0(A_358, k3_xboole_0(A_358, B_359))=k4_xboole_0(A_358, B_359))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3521])).
% 27.97/19.01  tff(c_7190, plain, (![A_358, B_359]: (r1_xboole_0(k4_xboole_0(A_358, B_359), k3_xboole_0(A_358, B_359)))), inference(superposition, [status(thm), theory('equality')], [c_7041, c_32])).
% 27.97/19.01  tff(c_22983, plain, (![B_578]: (r1_xboole_0(k3_subset_1(B_578, B_578), k3_xboole_0(B_578, B_578)))), inference(superposition, [status(thm), theory('equality')], [c_22886, c_7190])).
% 27.97/19.01  tff(c_23144, plain, (![B_578]: (r1_xboole_0(k3_subset_1(B_578, B_578), B_578))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_22983])).
% 27.97/19.01  tff(c_22873, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k3_subset_1(B_11, B_11))), inference(resolution, [status(thm)], [c_16, c_22337])).
% 27.97/19.01  tff(c_440, plain, (![B_11]: (k5_xboole_0(B_11, B_11)=k4_xboole_0(B_11, B_11))), inference(superposition, [status(thm), theory('equality')], [c_164, c_416])).
% 27.97/19.01  tff(c_22885, plain, (![B_11]: (k5_xboole_0(B_11, B_11)=k3_subset_1(B_11, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_22873, c_440])).
% 27.97/19.01  tff(c_223, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_108])).
% 27.97/19.01  tff(c_40, plain, (![C_43, A_39]: (r1_tarski(C_43, A_39) | ~r2_hidden(C_43, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 27.97/19.01  tff(c_227, plain, (![B_83, A_39]: (r1_tarski(B_83, A_39) | ~m1_subset_1(B_83, k1_zfmisc_1(A_39)) | v1_xboole_0(k1_zfmisc_1(A_39)))), inference(resolution, [status(thm)], [c_223, c_40])).
% 27.97/19.01  tff(c_231, plain, (![B_85, A_86]: (r1_tarski(B_85, A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)))), inference(negUnitSimplification, [status(thm)], [c_64, c_227])).
% 27.97/19.01  tff(c_243, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_231])).
% 27.97/19.01  tff(c_259, plain, (k3_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_243, c_24])).
% 27.97/19.01  tff(c_434, plain, (k5_xboole_0('#skF_6', '#skF_6')=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_259, c_416])).
% 27.97/19.01  tff(c_23525, plain, (k4_xboole_0('#skF_6', '#skF_4')=k3_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22885, c_434])).
% 27.97/19.01  tff(c_1061, plain, (![A_131, B_132]: (r1_tarski(A_131, k2_xboole_0(B_132, A_131)))), inference(resolution, [status(thm)], [c_26, c_1025])).
% 27.97/19.01  tff(c_1076, plain, (![A_131, B_132]: (k3_xboole_0(A_131, k2_xboole_0(B_132, A_131))=A_131)), inference(resolution, [status(thm)], [c_1061, c_24])).
% 27.97/19.01  tff(c_555, plain, (![A_105, C_106, B_107]: (r1_tarski(A_105, C_106) | ~r1_tarski(B_107, C_106) | ~r1_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.97/19.01  tff(c_892, plain, (![A_122, A_123, B_124]: (r1_tarski(A_122, A_123) | ~r1_tarski(A_122, k3_xboole_0(A_123, B_124)))), inference(resolution, [status(thm)], [c_20, c_555])).
% 27.97/19.01  tff(c_1569, plain, (![A_151, B_152, B_153]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_151, B_152), B_153), A_151))), inference(resolution, [status(thm)], [c_26, c_892])).
% 27.97/19.01  tff(c_1720, plain, (![B_157, A_158, B_159]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_157, A_158), B_159), A_158))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1569])).
% 27.97/19.01  tff(c_1751, plain, (![A_131, B_159, B_132]: (r1_tarski(k4_xboole_0(A_131, B_159), k2_xboole_0(B_132, A_131)))), inference(superposition, [status(thm), theory('equality')], [c_1076, c_1720])).
% 27.97/19.01  tff(c_26980, plain, (![B_618]: (r1_tarski(k3_subset_1('#skF_6', '#skF_6'), k2_xboole_0(B_618, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_23525, c_1751])).
% 27.97/19.01  tff(c_30, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, B_27) | ~r1_xboole_0(A_26, C_28) | ~r1_tarski(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.97/19.01  tff(c_26990, plain, (![B_618]: (r1_tarski(k3_subset_1('#skF_6', '#skF_6'), B_618) | ~r1_xboole_0(k3_subset_1('#skF_6', '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_26980, c_30])).
% 27.97/19.01  tff(c_27120, plain, (![B_621]: (r1_tarski(k3_subset_1('#skF_6', '#skF_6'), B_621))), inference(demodulation, [status(thm), theory('equality')], [c_23144, c_26990])).
% 27.97/19.01  tff(c_5462, plain, (![B_309, A_102, A_310]: (r1_xboole_0(B_309, A_102) | ~r1_tarski(A_102, k4_xboole_0(A_310, B_309)))), inference(superposition, [status(thm), theory('equality')], [c_5384, c_521])).
% 27.97/19.01  tff(c_27210, plain, (![B_309]: (r1_xboole_0(B_309, k3_subset_1('#skF_6', '#skF_6')))), inference(resolution, [status(thm)], [c_27120, c_5462])).
% 27.97/19.01  tff(c_27243, plain, (![B_622]: (r1_xboole_0(B_622, k3_subset_1('#skF_6', '#skF_6')))), inference(resolution, [status(thm)], [c_27120, c_5462])).
% 27.97/19.01  tff(c_5134, plain, (![B_37, C_38]: (k4_xboole_0(B_37, C_38)=B_37 | ~r1_xboole_0(B_37, C_38))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5119])).
% 27.97/19.01  tff(c_27341, plain, (![B_626]: (k4_xboole_0(B_626, k3_subset_1('#skF_6', '#skF_6'))=B_626)), inference(resolution, [status(thm)], [c_27243, c_5134])).
% 27.97/19.01  tff(c_244, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_231])).
% 27.97/19.01  tff(c_1522, plain, (![A_148, B_149, C_150]: (r1_tarski(A_148, k4_xboole_0(B_149, C_150)) | ~r1_xboole_0(A_148, C_150) | ~r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.97/19.01  tff(c_22, plain, (![A_16, C_18, B_17]: (r1_tarski(A_16, C_18) | ~r1_tarski(B_17, C_18) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.97/19.01  tff(c_9321, plain, (![A_405, B_406, C_407, A_408]: (r1_tarski(A_405, k4_xboole_0(B_406, C_407)) | ~r1_tarski(A_405, A_408) | ~r1_xboole_0(A_408, C_407) | ~r1_tarski(A_408, B_406))), inference(resolution, [status(thm)], [c_1522, c_22])).
% 27.97/19.01  tff(c_9623, plain, (![B_406, C_407]: (r1_tarski('#skF_5', k4_xboole_0(B_406, C_407)) | ~r1_xboole_0('#skF_4', C_407) | ~r1_tarski('#skF_4', B_406))), inference(resolution, [status(thm)], [c_244, c_9321])).
% 27.97/19.01  tff(c_27453, plain, (![B_626]: (r1_tarski('#skF_5', B_626) | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_6', '#skF_6')) | ~r1_tarski('#skF_4', B_626))), inference(superposition, [status(thm), theory('equality')], [c_27341, c_9623])).
% 27.97/19.01  tff(c_27662, plain, (![B_626]: (r1_tarski('#skF_5', B_626) | ~r1_tarski('#skF_4', B_626))), inference(demodulation, [status(thm), theory('equality')], [c_27210, c_27453])).
% 27.97/19.01  tff(c_28339, plain, (![B_637, B_638]: (r1_tarski(k3_subset_1(B_637, B_637), k2_xboole_0(B_638, B_637)))), inference(superposition, [status(thm), theory('equality')], [c_22886, c_1751])).
% 27.97/19.01  tff(c_28349, plain, (![B_637, B_638]: (r1_tarski(k3_subset_1(B_637, B_637), B_638) | ~r1_xboole_0(k3_subset_1(B_637, B_637), B_637))), inference(resolution, [status(thm)], [c_28339, c_30])).
% 27.97/19.01  tff(c_28417, plain, (![B_642, B_643]: (r1_tarski(k3_subset_1(B_642, B_642), B_643))), inference(demodulation, [status(thm), theory('equality')], [c_23144, c_28349])).
% 27.97/19.01  tff(c_28505, plain, (![B_309, B_642]: (r1_xboole_0(B_309, k3_subset_1(B_642, B_642)))), inference(resolution, [status(thm)], [c_28417, c_5462])).
% 27.97/19.01  tff(c_28657, plain, (![B_647, B_648]: (r1_xboole_0(B_647, k3_subset_1(B_648, B_648)))), inference(resolution, [status(thm)], [c_28417, c_5462])).
% 27.97/19.01  tff(c_28682, plain, (![B_647, B_648]: (k4_xboole_0(B_647, k3_subset_1(B_648, B_648))=B_647)), inference(resolution, [status(thm)], [c_28657, c_5134])).
% 27.97/19.01  tff(c_8592, plain, (![A_391, B_392, C_393]: (k3_xboole_0(A_391, k4_xboole_0(B_392, C_393))=A_391 | ~r1_xboole_0(A_391, C_393) | ~r1_tarski(A_391, B_392))), inference(resolution, [status(thm)], [c_1522, c_24])).
% 27.97/19.01  tff(c_39002, plain, (![B_821, C_822, B_823]: (k3_xboole_0(k4_xboole_0(B_821, C_822), B_823)=B_823 | ~r1_xboole_0(B_823, C_822) | ~r1_tarski(B_823, B_821))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8592])).
% 27.97/19.01  tff(c_39375, plain, (![B_647, B_823, B_648]: (k3_xboole_0(B_647, B_823)=B_823 | ~r1_xboole_0(B_823, k3_subset_1(B_648, B_648)) | ~r1_tarski(B_823, B_647))), inference(superposition, [status(thm), theory('equality')], [c_28682, c_39002])).
% 27.97/19.01  tff(c_60083, plain, (![B_1061, B_1062]: (k3_xboole_0(B_1061, B_1062)=B_1062 | ~r1_tarski(B_1062, B_1061))), inference(demodulation, [status(thm), theory('equality')], [c_28505, c_39375])).
% 27.97/19.01  tff(c_65943, plain, (![B_1145]: (k3_xboole_0(B_1145, '#skF_5')='#skF_5' | ~r1_tarski('#skF_4', B_1145))), inference(resolution, [status(thm)], [c_27662, c_60083])).
% 27.97/19.01  tff(c_66148, plain, (k3_xboole_0(k2_xboole_0('#skF_6', k3_subset_1('#skF_4', '#skF_6')), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_1445, c_65943])).
% 27.97/19.01  tff(c_75602, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_6', k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_66148, c_20])).
% 27.97/19.01  tff(c_75764, plain, (r1_tarski('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_75602, c_30])).
% 27.97/19.01  tff(c_75789, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21264, c_75764])).
% 27.97/19.01  tff(c_75791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_75789])).
% 27.97/19.01  tff(c_75793, plain, (r1_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 27.97/19.01  tff(c_76395, plain, (![A_1311, B_1312]: (k4_xboole_0(A_1311, B_1312)=k3_subset_1(A_1311, B_1312) | ~m1_subset_1(B_1312, k1_zfmisc_1(A_1311)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 27.97/19.01  tff(c_76411, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_76395])).
% 27.97/19.01  tff(c_75990, plain, (![A_1285, C_1286, B_1287]: (r1_xboole_0(A_1285, k4_xboole_0(C_1286, B_1287)) | ~r1_tarski(A_1285, B_1287))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.97/19.01  tff(c_77584, plain, (![C_1362, B_1363, A_1364]: (r1_xboole_0(k4_xboole_0(C_1362, B_1363), A_1364) | ~r1_tarski(A_1364, B_1363))), inference(resolution, [status(thm)], [c_75990, c_10])).
% 27.97/19.01  tff(c_77604, plain, (![A_1364]: (r1_xboole_0(k3_subset_1('#skF_4', '#skF_6'), A_1364) | ~r1_tarski(A_1364, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_76411, c_77584])).
% 27.97/19.01  tff(c_76423, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76411, c_26])).
% 27.97/19.01  tff(c_76412, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_76395])).
% 27.97/19.01  tff(c_76692, plain, (![A_1324, B_1325, C_1326]: (r1_tarski(A_1324, k4_xboole_0(B_1325, C_1326)) | ~r1_xboole_0(A_1324, C_1326) | ~r1_tarski(A_1324, B_1325))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.97/19.01  tff(c_82658, plain, (![A_1527]: (r1_tarski(A_1527, k3_subset_1('#skF_4', '#skF_5')) | ~r1_xboole_0(A_1527, '#skF_5') | ~r1_tarski(A_1527, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_76412, c_76692])).
% 27.97/19.01  tff(c_75792, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_70])).
% 27.97/19.01  tff(c_82698, plain, (~r1_xboole_0(k3_subset_1('#skF_4', '#skF_6'), '#skF_5') | ~r1_tarski(k3_subset_1('#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_82658, c_75792])).
% 27.97/19.01  tff(c_82716, plain, (~r1_xboole_0(k3_subset_1('#skF_4', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76423, c_82698])).
% 27.97/19.01  tff(c_82719, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_77604, c_82716])).
% 27.97/19.01  tff(c_82723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75793, c_82719])).
% 27.97/19.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.97/19.01  
% 27.97/19.01  Inference rules
% 27.97/19.01  ----------------------
% 27.97/19.01  #Ref     : 0
% 27.97/19.01  #Sup     : 20527
% 27.97/19.01  #Fact    : 0
% 27.97/19.01  #Define  : 0
% 27.97/19.01  #Split   : 28
% 27.97/19.01  #Chain   : 0
% 27.97/19.01  #Close   : 0
% 27.97/19.01  
% 27.97/19.01  Ordering : KBO
% 27.97/19.01  
% 27.97/19.01  Simplification rules
% 27.97/19.01  ----------------------
% 27.97/19.01  #Subsume      : 1597
% 27.97/19.01  #Demod        : 12677
% 27.97/19.01  #Tautology    : 8978
% 27.97/19.01  #SimpNegUnit  : 215
% 27.97/19.01  #BackRed      : 43
% 27.97/19.01  
% 27.97/19.01  #Partial instantiations: 0
% 27.97/19.01  #Strategies tried      : 1
% 27.97/19.01  
% 27.97/19.01  Timing (in seconds)
% 27.97/19.01  ----------------------
% 28.05/19.01  Preprocessing        : 0.35
% 28.05/19.01  Parsing              : 0.19
% 28.05/19.01  CNF conversion       : 0.02
% 28.05/19.01  Main loop            : 17.87
% 28.05/19.01  Inferencing          : 1.97
% 28.05/19.01  Reduction            : 9.86
% 28.05/19.01  Demodulation         : 8.65
% 28.05/19.01  BG Simplification    : 0.20
% 28.05/19.01  Subsumption          : 4.61
% 28.05/19.01  Abstraction          : 0.28
% 28.05/19.01  MUC search           : 0.00
% 28.05/19.01  Cooper               : 0.00
% 28.05/19.01  Total                : 18.27
% 28.05/19.01  Index Insertion      : 0.00
% 28.05/19.01  Index Deletion       : 0.00
% 28.05/19.01  Index Matching       : 0.00
% 28.05/19.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
