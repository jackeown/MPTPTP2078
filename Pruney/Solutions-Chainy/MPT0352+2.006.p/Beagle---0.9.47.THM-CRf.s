%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:47 EST 2020

% Result     : Theorem 12.73s
% Output     : CNFRefutation 12.73s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 156 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 263 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_60,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_151,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_206,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_66])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_748,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(A_113,B_114) = k3_subset_1(A_113,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_765,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_748])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4816,plain,(
    ! [A_215] :
      ( r1_xboole_0(A_215,'#skF_4')
      | ~ r1_tarski(A_215,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_16])).

tff(c_4843,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_4816])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4850,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4843,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_391,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(A_98,C_99)
      | ~ r1_tarski(k2_xboole_0(A_98,B_100),C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_434,plain,(
    ! [A_101,B_102] : r1_tarski(A_101,k2_xboole_0(A_101,B_102)) ),
    inference(resolution,[status(thm)],[c_12,c_391])).

tff(c_464,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_434])).

tff(c_28,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_948,plain,(
    ! [A_118,B_119,C_120] :
      ( r1_tarski(A_118,B_119)
      | ~ r1_xboole_0(A_118,C_120)
      | ~ r1_tarski(A_118,k2_xboole_0(B_119,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3563,plain,(
    ! [A_182,B_183,A_184] :
      ( r1_tarski(A_182,B_183)
      | ~ r1_xboole_0(A_182,A_184)
      | ~ r1_tarski(A_182,k2_xboole_0(A_184,B_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_948])).

tff(c_22599,plain,(
    ! [A_430,B_431,A_432] :
      ( r1_tarski(A_430,k4_xboole_0(B_431,A_432))
      | ~ r1_xboole_0(A_430,A_432)
      | ~ r1_tarski(A_430,k2_xboole_0(A_432,B_431)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3563])).

tff(c_186,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(A_62,B_63)
      | ~ r1_tarski(A_62,k4_xboole_0(B_63,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_191,plain,(
    ! [B_63,C_64] : r1_tarski(k4_xboole_0(B_63,C_64),B_63) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_283,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_294,plain,(
    ! [B_63,C_64] :
      ( k4_xboole_0(B_63,C_64) = B_63
      | ~ r1_tarski(B_63,k4_xboole_0(B_63,C_64)) ) ),
    inference(resolution,[status(thm)],[c_191,c_283])).

tff(c_22633,plain,(
    ! [B_431,A_432] :
      ( k4_xboole_0(B_431,A_432) = B_431
      | ~ r1_xboole_0(B_431,A_432)
      | ~ r1_tarski(B_431,k2_xboole_0(A_432,B_431)) ) ),
    inference(resolution,[status(thm)],[c_22599,c_294])).

tff(c_23938,plain,(
    ! [B_455,A_456] :
      ( k4_xboole_0(B_455,A_456) = B_455
      | ~ r1_xboole_0(B_455,A_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_22633])).

tff(c_24042,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4850,c_23938])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_764,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_748])).

tff(c_54,plain,(
    ! [A_38] : ~ v1_xboole_0(k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_609,plain,(
    ! [B_109,A_110] :
      ( r2_hidden(B_109,A_110)
      | ~ m1_subset_1(B_109,A_110)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [C_33,A_29] :
      ( r1_tarski(C_33,A_29)
      | ~ r2_hidden(C_33,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_616,plain,(
    ! [B_109,A_29] :
      ( r1_tarski(B_109,A_29)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_29))
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_609,c_32])).

tff(c_623,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_112)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_616])).

tff(c_640,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_623])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_662,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_640,c_22])).

tff(c_192,plain,(
    ! [B_65,C_66] : r1_tarski(k4_xboole_0(B_65,C_66),B_65) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_205,plain,(
    ! [B_65,C_66] : k2_xboole_0(k4_xboole_0(B_65,C_66),B_65) = B_65 ),
    inference(resolution,[status(thm)],[c_192,c_22])).

tff(c_20,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,C_16)
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1819,plain,(
    ! [A_143,B_144,B_145] : r1_tarski(A_143,k2_xboole_0(k2_xboole_0(A_143,B_144),B_145)) ),
    inference(resolution,[status(thm)],[c_434,c_20])).

tff(c_2913,plain,(
    ! [B_170,C_171,B_172] : r1_tarski(k4_xboole_0(B_170,C_171),k2_xboole_0(B_170,B_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_1819])).

tff(c_3071,plain,(
    ! [C_174] : r1_tarski(k4_xboole_0('#skF_4',C_174),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_2913])).

tff(c_3105,plain,(
    ! [C_176] : k2_xboole_0(k4_xboole_0('#skF_4',C_176),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3071,c_22])).

tff(c_1912,plain,(
    ! [A_143,A_1,B_144] : r1_tarski(A_143,k2_xboole_0(A_1,k2_xboole_0(A_143,B_144))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1819])).

tff(c_3116,plain,(
    ! [C_176,A_1] : r1_tarski(k4_xboole_0('#skF_4',C_176),k2_xboole_0(A_1,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3105,c_1912])).

tff(c_299,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_xboole_0(A_78,C_79)
      | ~ r1_tarski(A_78,k4_xboole_0(B_80,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_314,plain,(
    ! [B_80,C_79] : r1_xboole_0(k4_xboole_0(B_80,C_79),C_79) ),
    inference(resolution,[status(thm)],[c_12,c_299])).

tff(c_4163,plain,(
    ! [A_195,A_196,B_197] :
      ( r1_tarski(A_195,A_196)
      | ~ r1_xboole_0(A_195,k4_xboole_0(B_197,A_196))
      | ~ r1_tarski(A_195,k2_xboole_0(A_196,B_197)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_948])).

tff(c_30657,plain,(
    ! [B_541,B_542,A_543] :
      ( r1_tarski(k4_xboole_0(B_541,k4_xboole_0(B_542,A_543)),A_543)
      | ~ r1_tarski(k4_xboole_0(B_541,k4_xboole_0(B_542,A_543)),k2_xboole_0(A_543,B_542)) ) ),
    inference(resolution,[status(thm)],[c_314,c_4163])).

tff(c_31206,plain,(
    ! [A_546] : r1_tarski(k4_xboole_0('#skF_4',k4_xboole_0('#skF_3',A_546)),A_546) ),
    inference(resolution,[status(thm)],[c_3116,c_30657])).

tff(c_31299,plain,(
    r1_tarski(k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_31206])).

tff(c_31327,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24042,c_31299])).

tff(c_31329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_31327])).

tff(c_31330,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_31331,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_32690,plain,(
    ! [A_611,B_612] :
      ( k4_xboole_0(A_611,B_612) = k3_subset_1(A_611,B_612)
      | ~ m1_subset_1(B_612,k1_zfmisc_1(A_611)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32703,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_32690])).

tff(c_32702,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_32690])).

tff(c_26,plain,(
    ! [C_23,B_22,A_21] :
      ( r1_tarski(k4_xboole_0(C_23,B_22),k4_xboole_0(C_23,A_21))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38124,plain,(
    ! [A_756] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',A_756))
      | ~ r1_tarski(A_756,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32702,c_26])).

tff(c_38145,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32703,c_38124])).

tff(c_38158,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31331,c_38145])).

tff(c_38160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31330,c_38158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:11:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.73/5.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.73/5.69  
% 12.73/5.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.73/5.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 12.73/5.69  
% 12.73/5.69  %Foreground sorts:
% 12.73/5.69  
% 12.73/5.69  
% 12.73/5.69  %Background operators:
% 12.73/5.69  
% 12.73/5.69  
% 12.73/5.69  %Foreground operators:
% 12.73/5.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.73/5.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.73/5.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.73/5.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.73/5.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.73/5.69  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.73/5.69  tff('#skF_5', type, '#skF_5': $i).
% 12.73/5.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.73/5.69  tff('#skF_3', type, '#skF_3': $i).
% 12.73/5.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.73/5.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.73/5.69  tff('#skF_4', type, '#skF_4': $i).
% 12.73/5.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.73/5.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.73/5.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.73/5.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.73/5.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.73/5.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.73/5.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.73/5.69  
% 12.73/5.71  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 12.73/5.71  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.73/5.71  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 12.73/5.71  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.73/5.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.73/5.71  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.73/5.71  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 12.73/5.71  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.73/5.71  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 12.73/5.71  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.73/5.71  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 12.73/5.71  tff(f_78, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.73/5.71  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.73/5.71  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 12.73/5.71  tff(c_60, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.73/5.71  tff(c_151, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 12.73/5.71  tff(c_66, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.73/5.71  tff(c_206, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_151, c_66])).
% 12.73/5.71  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.73/5.71  tff(c_748, plain, (![A_113, B_114]: (k4_xboole_0(A_113, B_114)=k3_subset_1(A_113, B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.73/5.71  tff(c_765, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_748])).
% 12.73/5.71  tff(c_16, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, C_13) | ~r1_tarski(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.73/5.71  tff(c_4816, plain, (![A_215]: (r1_xboole_0(A_215, '#skF_4') | ~r1_tarski(A_215, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_765, c_16])).
% 12.73/5.71  tff(c_4843, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_206, c_4816])).
% 12.73/5.71  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.73/5.71  tff(c_4850, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_4843, c_6])).
% 12.73/5.71  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.73/5.71  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.73/5.71  tff(c_391, plain, (![A_98, C_99, B_100]: (r1_tarski(A_98, C_99) | ~r1_tarski(k2_xboole_0(A_98, B_100), C_99))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.73/5.71  tff(c_434, plain, (![A_101, B_102]: (r1_tarski(A_101, k2_xboole_0(A_101, B_102)))), inference(resolution, [status(thm)], [c_12, c_391])).
% 12.73/5.71  tff(c_464, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_434])).
% 12.73/5.71  tff(c_28, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.73/5.71  tff(c_948, plain, (![A_118, B_119, C_120]: (r1_tarski(A_118, B_119) | ~r1_xboole_0(A_118, C_120) | ~r1_tarski(A_118, k2_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.73/5.71  tff(c_3563, plain, (![A_182, B_183, A_184]: (r1_tarski(A_182, B_183) | ~r1_xboole_0(A_182, A_184) | ~r1_tarski(A_182, k2_xboole_0(A_184, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_948])).
% 12.73/5.71  tff(c_22599, plain, (![A_430, B_431, A_432]: (r1_tarski(A_430, k4_xboole_0(B_431, A_432)) | ~r1_xboole_0(A_430, A_432) | ~r1_tarski(A_430, k2_xboole_0(A_432, B_431)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3563])).
% 12.73/5.71  tff(c_186, plain, (![A_62, B_63, C_64]: (r1_tarski(A_62, B_63) | ~r1_tarski(A_62, k4_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.73/5.71  tff(c_191, plain, (![B_63, C_64]: (r1_tarski(k4_xboole_0(B_63, C_64), B_63))), inference(resolution, [status(thm)], [c_12, c_186])).
% 12.73/5.71  tff(c_283, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.73/5.71  tff(c_294, plain, (![B_63, C_64]: (k4_xboole_0(B_63, C_64)=B_63 | ~r1_tarski(B_63, k4_xboole_0(B_63, C_64)))), inference(resolution, [status(thm)], [c_191, c_283])).
% 12.73/5.71  tff(c_22633, plain, (![B_431, A_432]: (k4_xboole_0(B_431, A_432)=B_431 | ~r1_xboole_0(B_431, A_432) | ~r1_tarski(B_431, k2_xboole_0(A_432, B_431)))), inference(resolution, [status(thm)], [c_22599, c_294])).
% 12.73/5.71  tff(c_23938, plain, (![B_455, A_456]: (k4_xboole_0(B_455, A_456)=B_455 | ~r1_xboole_0(B_455, A_456))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_22633])).
% 12.73/5.71  tff(c_24042, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_4850, c_23938])).
% 12.73/5.71  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.73/5.71  tff(c_764, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_748])).
% 12.73/5.71  tff(c_54, plain, (![A_38]: (~v1_xboole_0(k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.73/5.71  tff(c_609, plain, (![B_109, A_110]: (r2_hidden(B_109, A_110) | ~m1_subset_1(B_109, A_110) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.73/5.71  tff(c_32, plain, (![C_33, A_29]: (r1_tarski(C_33, A_29) | ~r2_hidden(C_33, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.73/5.71  tff(c_616, plain, (![B_109, A_29]: (r1_tarski(B_109, A_29) | ~m1_subset_1(B_109, k1_zfmisc_1(A_29)) | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(resolution, [status(thm)], [c_609, c_32])).
% 12.73/5.71  tff(c_623, plain, (![B_111, A_112]: (r1_tarski(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(A_112)))), inference(negUnitSimplification, [status(thm)], [c_54, c_616])).
% 12.73/5.71  tff(c_640, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_623])).
% 12.73/5.71  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.73/5.71  tff(c_662, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_640, c_22])).
% 12.73/5.71  tff(c_192, plain, (![B_65, C_66]: (r1_tarski(k4_xboole_0(B_65, C_66), B_65))), inference(resolution, [status(thm)], [c_12, c_186])).
% 12.73/5.71  tff(c_205, plain, (![B_65, C_66]: (k2_xboole_0(k4_xboole_0(B_65, C_66), B_65)=B_65)), inference(resolution, [status(thm)], [c_192, c_22])).
% 12.73/5.71  tff(c_20, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, C_16) | ~r1_tarski(k2_xboole_0(A_14, B_15), C_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.73/5.71  tff(c_1819, plain, (![A_143, B_144, B_145]: (r1_tarski(A_143, k2_xboole_0(k2_xboole_0(A_143, B_144), B_145)))), inference(resolution, [status(thm)], [c_434, c_20])).
% 12.73/5.71  tff(c_2913, plain, (![B_170, C_171, B_172]: (r1_tarski(k4_xboole_0(B_170, C_171), k2_xboole_0(B_170, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_205, c_1819])).
% 12.73/5.71  tff(c_3071, plain, (![C_174]: (r1_tarski(k4_xboole_0('#skF_4', C_174), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_2913])).
% 12.73/5.71  tff(c_3105, plain, (![C_176]: (k2_xboole_0(k4_xboole_0('#skF_4', C_176), '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_3071, c_22])).
% 12.73/5.71  tff(c_1912, plain, (![A_143, A_1, B_144]: (r1_tarski(A_143, k2_xboole_0(A_1, k2_xboole_0(A_143, B_144))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1819])).
% 12.73/5.71  tff(c_3116, plain, (![C_176, A_1]: (r1_tarski(k4_xboole_0('#skF_4', C_176), k2_xboole_0(A_1, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3105, c_1912])).
% 12.73/5.71  tff(c_299, plain, (![A_78, C_79, B_80]: (r1_xboole_0(A_78, C_79) | ~r1_tarski(A_78, k4_xboole_0(B_80, C_79)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.73/5.71  tff(c_314, plain, (![B_80, C_79]: (r1_xboole_0(k4_xboole_0(B_80, C_79), C_79))), inference(resolution, [status(thm)], [c_12, c_299])).
% 12.73/5.71  tff(c_4163, plain, (![A_195, A_196, B_197]: (r1_tarski(A_195, A_196) | ~r1_xboole_0(A_195, k4_xboole_0(B_197, A_196)) | ~r1_tarski(A_195, k2_xboole_0(A_196, B_197)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_948])).
% 12.73/5.71  tff(c_30657, plain, (![B_541, B_542, A_543]: (r1_tarski(k4_xboole_0(B_541, k4_xboole_0(B_542, A_543)), A_543) | ~r1_tarski(k4_xboole_0(B_541, k4_xboole_0(B_542, A_543)), k2_xboole_0(A_543, B_542)))), inference(resolution, [status(thm)], [c_314, c_4163])).
% 12.73/5.71  tff(c_31206, plain, (![A_546]: (r1_tarski(k4_xboole_0('#skF_4', k4_xboole_0('#skF_3', A_546)), A_546))), inference(resolution, [status(thm)], [c_3116, c_30657])).
% 12.73/5.71  tff(c_31299, plain, (r1_tarski(k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_764, c_31206])).
% 12.73/5.71  tff(c_31327, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24042, c_31299])).
% 12.73/5.71  tff(c_31329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_31327])).
% 12.73/5.71  tff(c_31330, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 12.73/5.71  tff(c_31331, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 12.73/5.71  tff(c_32690, plain, (![A_611, B_612]: (k4_xboole_0(A_611, B_612)=k3_subset_1(A_611, B_612) | ~m1_subset_1(B_612, k1_zfmisc_1(A_611)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.73/5.71  tff(c_32703, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_32690])).
% 12.73/5.71  tff(c_32702, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_32690])).
% 12.73/5.71  tff(c_26, plain, (![C_23, B_22, A_21]: (r1_tarski(k4_xboole_0(C_23, B_22), k4_xboole_0(C_23, A_21)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.73/5.71  tff(c_38124, plain, (![A_756]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', A_756)) | ~r1_tarski(A_756, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32702, c_26])).
% 12.73/5.71  tff(c_38145, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32703, c_38124])).
% 12.73/5.71  tff(c_38158, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31331, c_38145])).
% 12.73/5.71  tff(c_38160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31330, c_38158])).
% 12.73/5.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.73/5.71  
% 12.73/5.71  Inference rules
% 12.73/5.71  ----------------------
% 12.73/5.71  #Ref     : 0
% 12.73/5.71  #Sup     : 9469
% 12.73/5.71  #Fact    : 0
% 12.73/5.71  #Define  : 0
% 12.73/5.71  #Split   : 12
% 12.73/5.71  #Chain   : 0
% 12.73/5.71  #Close   : 0
% 12.73/5.71  
% 12.73/5.71  Ordering : KBO
% 12.73/5.71  
% 12.73/5.71  Simplification rules
% 12.73/5.71  ----------------------
% 12.73/5.71  #Subsume      : 807
% 12.73/5.71  #Demod        : 7086
% 12.73/5.71  #Tautology    : 5694
% 12.73/5.71  #SimpNegUnit  : 73
% 12.73/5.71  #BackRed      : 24
% 12.73/5.71  
% 12.73/5.71  #Partial instantiations: 0
% 12.73/5.71  #Strategies tried      : 1
% 12.73/5.71  
% 12.73/5.71  Timing (in seconds)
% 12.73/5.71  ----------------------
% 12.73/5.71  Preprocessing        : 0.33
% 12.73/5.71  Parsing              : 0.18
% 12.73/5.71  CNF conversion       : 0.02
% 12.73/5.71  Main loop            : 4.67
% 12.73/5.71  Inferencing          : 0.85
% 12.73/5.71  Reduction            : 2.33
% 12.73/5.71  Demodulation         : 1.90
% 12.73/5.71  BG Simplification    : 0.09
% 12.73/5.71  Subsumption          : 1.03
% 12.73/5.71  Abstraction          : 0.12
% 12.73/5.71  MUC search           : 0.00
% 12.73/5.71  Cooper               : 0.00
% 12.73/5.71  Total                : 5.04
% 12.73/5.71  Index Insertion      : 0.00
% 12.73/5.71  Index Deletion       : 0.00
% 12.73/5.71  Index Matching       : 0.00
% 12.73/5.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
