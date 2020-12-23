%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:25 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 158 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 232 expanded)
%              Number of equality atoms :   44 ( 104 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_48,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_171,plain,(
    k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_28,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_87,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_104,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_131,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_1272,plain,(
    ! [A_137,B_138,C_139] :
      ( r2_hidden('#skF_1'(A_137,B_138,C_139),A_137)
      | r2_hidden('#skF_2'(A_137,B_138,C_139),C_139)
      | k4_xboole_0(A_137,B_138) = C_139 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1275,plain,(
    ! [A_137,C_139] :
      ( r2_hidden('#skF_2'(A_137,A_137,C_139),C_139)
      | k4_xboole_0(A_137,A_137) = C_139 ) ),
    inference(resolution,[status(thm)],[c_1272,c_16])).

tff(c_6443,plain,(
    ! [A_291,C_292] :
      ( r2_hidden('#skF_2'(A_291,A_291,C_292),C_292)
      | k3_xboole_0(A_291,k1_xboole_0) = C_292 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1275])).

tff(c_60,plain,(
    ! [A_34,B_35] : r1_xboole_0(k4_xboole_0(A_34,B_35),B_35) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_63,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_60])).

tff(c_134,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k3_xboole_0(A_52,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_156,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_28])).

tff(c_445,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,k3_xboole_0(A_72,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_448,plain,(
    ! [C_74] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_74,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_445])).

tff(c_450,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_448])).

tff(c_6500,plain,(
    ! [A_291] : k3_xboole_0(A_291,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6443,c_450])).

tff(c_1319,plain,(
    ! [A_137,C_139] :
      ( r2_hidden('#skF_2'(A_137,A_137,C_139),C_139)
      | k3_xboole_0(A_137,k1_xboole_0) = C_139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1275])).

tff(c_9854,plain,(
    ! [A_342,C_343] :
      ( r2_hidden('#skF_2'(A_342,A_342,C_343),C_343)
      | k1_xboole_0 = C_343 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6500,c_1319])).

tff(c_24,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9901,plain,(
    ! [A_344,B_345] :
      ( ~ r1_xboole_0(A_344,B_345)
      | k3_xboole_0(A_344,B_345) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9854,c_24])).

tff(c_10009,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_9901])).

tff(c_34,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10163,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10009,c_34])).

tff(c_10186,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10163])).

tff(c_10188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_10186])).

tff(c_10189,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_42,plain,(
    ! [A_31,B_32] : r1_xboole_0(k4_xboole_0(A_31,B_32),B_32) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10206,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10189,c_42])).

tff(c_10210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_10206])).

tff(c_10211,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_10219,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10211,c_42])).

tff(c_10223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_10219])).

tff(c_10225,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10251,plain,(
    k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10225,c_44])).

tff(c_10224,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_10257,plain,(
    ! [A_353,B_354] : k4_xboole_0(A_353,k4_xboole_0(A_353,B_354)) = k3_xboole_0(A_353,B_354) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10281,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10257])).

tff(c_11333,plain,(
    ! [A_435,B_436,C_437] :
      ( r2_hidden('#skF_1'(A_435,B_436,C_437),A_435)
      | r2_hidden('#skF_2'(A_435,B_436,C_437),C_437)
      | k4_xboole_0(A_435,B_436) = C_437 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11336,plain,(
    ! [A_435,C_437] :
      ( r2_hidden('#skF_2'(A_435,A_435,C_437),C_437)
      | k4_xboole_0(A_435,A_435) = C_437 ) ),
    inference(resolution,[status(thm)],[c_11333,c_16])).

tff(c_14966,plain,(
    ! [A_551,C_552] :
      ( r2_hidden('#skF_2'(A_551,A_551,C_552),C_552)
      | k3_xboole_0(A_551,k1_xboole_0) = C_552 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10281,c_11336])).

tff(c_65,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_63,c_65])).

tff(c_10284,plain,(
    ! [A_355] : k4_xboole_0(A_355,A_355) = k3_xboole_0(A_355,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10257])).

tff(c_10303,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10284,c_28])).

tff(c_10449,plain,(
    ! [A_370,B_371,C_372] :
      ( ~ r1_xboole_0(A_370,B_371)
      | ~ r2_hidden(C_372,k3_xboole_0(A_370,B_371)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10452,plain,(
    ! [C_372] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_372,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10303,c_10449])).

tff(c_10454,plain,(
    ! [C_372] : ~ r2_hidden(C_372,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10452])).

tff(c_15008,plain,(
    ! [A_551] : k3_xboole_0(A_551,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14966,c_10454])).

tff(c_11384,plain,(
    ! [A_435,C_437] :
      ( r2_hidden('#skF_2'(A_435,A_435,C_437),C_437)
      | k3_xboole_0(A_435,k1_xboole_0) = C_437 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10281,c_11336])).

tff(c_17486,plain,(
    ! [A_602,C_603] :
      ( r2_hidden('#skF_2'(A_602,A_602,C_603),C_603)
      | k1_xboole_0 = C_603 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15008,c_11384])).

tff(c_17538,plain,(
    ! [A_604,B_605] :
      ( ~ r1_xboole_0(A_604,B_605)
      | k3_xboole_0(A_604,B_605) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_17486,c_24])).

tff(c_17636,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10224,c_17538])).

tff(c_18006,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_17636,c_34])).

tff(c_18029,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18006])).

tff(c_18031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10251,c_18029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.91/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/2.73  
% 7.91/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/2.74  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.91/2.74  
% 7.91/2.74  %Foreground sorts:
% 7.91/2.74  
% 7.91/2.74  
% 7.91/2.74  %Background operators:
% 7.91/2.74  
% 7.91/2.74  
% 7.91/2.74  %Foreground operators:
% 7.91/2.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.91/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.91/2.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.91/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.91/2.74  tff('#skF_7', type, '#skF_7': $i).
% 7.91/2.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.91/2.74  tff('#skF_5', type, '#skF_5': $i).
% 7.91/2.74  tff('#skF_6', type, '#skF_6': $i).
% 7.91/2.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.91/2.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.91/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/2.74  tff('#skF_4', type, '#skF_4': $i).
% 7.91/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/2.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.91/2.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.91/2.74  
% 7.91/2.75  tff(f_78, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.91/2.75  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.91/2.75  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.91/2.75  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.91/2.75  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.91/2.75  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.91/2.75  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.91/2.75  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.91/2.75  tff(c_48, plain, (~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.91/2.75  tff(c_77, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 7.91/2.75  tff(c_46, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4' | k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.91/2.75  tff(c_171, plain, (k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_46])).
% 7.91/2.75  tff(c_28, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.91/2.75  tff(c_50, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4' | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.91/2.75  tff(c_87, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 7.91/2.75  tff(c_104, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.91/2.75  tff(c_131, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_104])).
% 7.91/2.75  tff(c_1272, plain, (![A_137, B_138, C_139]: (r2_hidden('#skF_1'(A_137, B_138, C_139), A_137) | r2_hidden('#skF_2'(A_137, B_138, C_139), C_139) | k4_xboole_0(A_137, B_138)=C_139)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.91/2.75  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.91/2.75  tff(c_1275, plain, (![A_137, C_139]: (r2_hidden('#skF_2'(A_137, A_137, C_139), C_139) | k4_xboole_0(A_137, A_137)=C_139)), inference(resolution, [status(thm)], [c_1272, c_16])).
% 7.91/2.75  tff(c_6443, plain, (![A_291, C_292]: (r2_hidden('#skF_2'(A_291, A_291, C_292), C_292) | k3_xboole_0(A_291, k1_xboole_0)=C_292)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1275])).
% 7.91/2.75  tff(c_60, plain, (![A_34, B_35]: (r1_xboole_0(k4_xboole_0(A_34, B_35), B_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.91/2.75  tff(c_63, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_60])).
% 7.91/2.75  tff(c_134, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k3_xboole_0(A_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_104])).
% 7.91/2.75  tff(c_156, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_134, c_28])).
% 7.91/2.75  tff(c_445, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, k3_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.91/2.75  tff(c_448, plain, (![C_74]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_156, c_445])).
% 7.91/2.75  tff(c_450, plain, (![C_74]: (~r2_hidden(C_74, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_448])).
% 7.91/2.75  tff(c_6500, plain, (![A_291]: (k3_xboole_0(A_291, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6443, c_450])).
% 7.91/2.75  tff(c_1319, plain, (![A_137, C_139]: (r2_hidden('#skF_2'(A_137, A_137, C_139), C_139) | k3_xboole_0(A_137, k1_xboole_0)=C_139)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1275])).
% 7.91/2.75  tff(c_9854, plain, (![A_342, C_343]: (r2_hidden('#skF_2'(A_342, A_342, C_343), C_343) | k1_xboole_0=C_343)), inference(demodulation, [status(thm), theory('equality')], [c_6500, c_1319])).
% 7.91/2.75  tff(c_24, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.91/2.75  tff(c_9901, plain, (![A_344, B_345]: (~r1_xboole_0(A_344, B_345) | k3_xboole_0(A_344, B_345)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9854, c_24])).
% 7.91/2.75  tff(c_10009, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_9901])).
% 7.91/2.75  tff(c_34, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.91/2.75  tff(c_10163, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10009, c_34])).
% 7.91/2.75  tff(c_10186, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10163])).
% 7.91/2.75  tff(c_10188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_10186])).
% 7.91/2.75  tff(c_10189, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 7.91/2.75  tff(c_42, plain, (![A_31, B_32]: (r1_xboole_0(k4_xboole_0(A_31, B_32), B_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.91/2.75  tff(c_10206, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10189, c_42])).
% 7.91/2.75  tff(c_10210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_10206])).
% 7.91/2.75  tff(c_10211, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 7.91/2.75  tff(c_10219, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10211, c_42])).
% 7.91/2.75  tff(c_10223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_10219])).
% 7.91/2.75  tff(c_10225, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 7.91/2.75  tff(c_44, plain, (~r1_xboole_0('#skF_4', '#skF_5') | k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.91/2.75  tff(c_10251, plain, (k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10225, c_44])).
% 7.91/2.75  tff(c_10224, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 7.91/2.75  tff(c_10257, plain, (![A_353, B_354]: (k4_xboole_0(A_353, k4_xboole_0(A_353, B_354))=k3_xboole_0(A_353, B_354))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.91/2.75  tff(c_10281, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_10257])).
% 7.91/2.75  tff(c_11333, plain, (![A_435, B_436, C_437]: (r2_hidden('#skF_1'(A_435, B_436, C_437), A_435) | r2_hidden('#skF_2'(A_435, B_436, C_437), C_437) | k4_xboole_0(A_435, B_436)=C_437)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.91/2.75  tff(c_11336, plain, (![A_435, C_437]: (r2_hidden('#skF_2'(A_435, A_435, C_437), C_437) | k4_xboole_0(A_435, A_435)=C_437)), inference(resolution, [status(thm)], [c_11333, c_16])).
% 7.91/2.75  tff(c_14966, plain, (![A_551, C_552]: (r2_hidden('#skF_2'(A_551, A_551, C_552), C_552) | k3_xboole_0(A_551, k1_xboole_0)=C_552)), inference(demodulation, [status(thm), theory('equality')], [c_10281, c_11336])).
% 7.91/2.75  tff(c_65, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.91/2.75  tff(c_70, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_63, c_65])).
% 7.91/2.75  tff(c_10284, plain, (![A_355]: (k4_xboole_0(A_355, A_355)=k3_xboole_0(A_355, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_10257])).
% 7.91/2.75  tff(c_10303, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10284, c_28])).
% 7.91/2.75  tff(c_10449, plain, (![A_370, B_371, C_372]: (~r1_xboole_0(A_370, B_371) | ~r2_hidden(C_372, k3_xboole_0(A_370, B_371)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.91/2.75  tff(c_10452, plain, (![C_372]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_372, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10303, c_10449])).
% 7.91/2.75  tff(c_10454, plain, (![C_372]: (~r2_hidden(C_372, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10452])).
% 7.91/2.75  tff(c_15008, plain, (![A_551]: (k3_xboole_0(A_551, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14966, c_10454])).
% 7.91/2.75  tff(c_11384, plain, (![A_435, C_437]: (r2_hidden('#skF_2'(A_435, A_435, C_437), C_437) | k3_xboole_0(A_435, k1_xboole_0)=C_437)), inference(demodulation, [status(thm), theory('equality')], [c_10281, c_11336])).
% 7.91/2.75  tff(c_17486, plain, (![A_602, C_603]: (r2_hidden('#skF_2'(A_602, A_602, C_603), C_603) | k1_xboole_0=C_603)), inference(demodulation, [status(thm), theory('equality')], [c_15008, c_11384])).
% 7.91/2.75  tff(c_17538, plain, (![A_604, B_605]: (~r1_xboole_0(A_604, B_605) | k3_xboole_0(A_604, B_605)=k1_xboole_0)), inference(resolution, [status(thm)], [c_17486, c_24])).
% 7.91/2.75  tff(c_17636, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_10224, c_17538])).
% 7.91/2.75  tff(c_18006, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17636, c_34])).
% 7.91/2.75  tff(c_18029, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18006])).
% 7.91/2.75  tff(c_18031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10251, c_18029])).
% 7.91/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/2.75  
% 7.91/2.75  Inference rules
% 7.91/2.75  ----------------------
% 7.91/2.75  #Ref     : 2
% 7.91/2.75  #Sup     : 4392
% 7.91/2.75  #Fact    : 0
% 7.91/2.75  #Define  : 0
% 7.91/2.75  #Split   : 3
% 7.91/2.75  #Chain   : 0
% 7.91/2.75  #Close   : 0
% 7.91/2.75  
% 7.91/2.75  Ordering : KBO
% 7.91/2.75  
% 7.91/2.75  Simplification rules
% 7.91/2.75  ----------------------
% 7.91/2.75  #Subsume      : 343
% 7.91/2.75  #Demod        : 3724
% 7.91/2.75  #Tautology    : 2717
% 7.91/2.75  #SimpNegUnit  : 55
% 7.91/2.75  #BackRed      : 64
% 7.91/2.75  
% 7.91/2.75  #Partial instantiations: 0
% 7.91/2.75  #Strategies tried      : 1
% 7.91/2.75  
% 7.91/2.75  Timing (in seconds)
% 7.91/2.75  ----------------------
% 7.91/2.75  Preprocessing        : 0.31
% 7.91/2.75  Parsing              : 0.16
% 7.91/2.75  CNF conversion       : 0.02
% 7.91/2.75  Main loop            : 1.69
% 7.91/2.75  Inferencing          : 0.50
% 7.91/2.75  Reduction            : 0.72
% 7.91/2.75  Demodulation         : 0.56
% 7.91/2.75  BG Simplification    : 0.06
% 7.91/2.76  Subsumption          : 0.30
% 7.91/2.76  Abstraction          : 0.08
% 7.91/2.76  MUC search           : 0.00
% 7.91/2.76  Cooper               : 0.00
% 7.91/2.76  Total                : 2.03
% 7.91/2.76  Index Insertion      : 0.00
% 7.91/2.76  Index Deletion       : 0.00
% 7.91/2.76  Index Matching       : 0.00
% 7.91/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
