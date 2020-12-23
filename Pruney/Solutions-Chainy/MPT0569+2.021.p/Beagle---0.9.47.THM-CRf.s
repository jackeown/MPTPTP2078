%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:38 EST 2020

% Result     : Theorem 37.60s
% Output     : CNFRefutation 37.60s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 187 expanded)
%              Number of leaves         :   34 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 ( 293 expanded)
%              Number of equality atoms :   35 ( 111 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

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

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11')
    | k10_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_85,plain,(
    k10_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,k3_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    ! [A_11,C_90] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_90,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_87])).

tff(c_101,plain,(
    ! [C_90] : ~ r2_hidden(C_90,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_54,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_151,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_151])).

tff(c_184,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_62,plain,
    ( k10_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_96,plain,(
    r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_62])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    k4_xboole_0(k2_relat_1('#skF_12'),'#skF_11') = k2_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_96,c_18])).

tff(c_170,plain,(
    k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_12')) = k3_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_151])).

tff(c_214,plain,(
    k3_xboole_0(k2_relat_1('#skF_12'),'#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_170])).

tff(c_739,plain,(
    ! [B_143,A_144] :
      ( k10_relat_1(B_143,k3_xboole_0(k2_relat_1(B_143),A_144)) = k10_relat_1(B_143,A_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_764,plain,
    ( k10_relat_1('#skF_12',k1_xboole_0) = k10_relat_1('#skF_12','#skF_11')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_739])).

tff(c_769,plain,(
    k10_relat_1('#skF_12',k1_xboole_0) = k10_relat_1('#skF_12','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_764])).

tff(c_1587,plain,(
    ! [A_184,B_185,D_186] :
      ( r2_hidden('#skF_6'(A_184,B_185,k10_relat_1(A_184,B_185),D_186),B_185)
      | ~ r2_hidden(D_186,k10_relat_1(A_184,B_185))
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1607,plain,(
    ! [D_186] :
      ( r2_hidden('#skF_6'('#skF_12',k1_xboole_0,k10_relat_1('#skF_12','#skF_11'),D_186),k1_xboole_0)
      | ~ r2_hidden(D_186,k10_relat_1('#skF_12',k1_xboole_0))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_1587])).

tff(c_1617,plain,(
    ! [D_186] :
      ( r2_hidden('#skF_6'('#skF_12',k1_xboole_0,k10_relat_1('#skF_12','#skF_11'),D_186),k1_xboole_0)
      | ~ r2_hidden(D_186,k10_relat_1('#skF_12','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_769,c_1607])).

tff(c_1619,plain,(
    ! [D_187] : ~ r2_hidden(D_187,k10_relat_1('#skF_12','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1617])).

tff(c_1682,plain,(
    ! [B_191] : r1_xboole_0(k10_relat_1('#skF_12','#skF_11'),B_191) ),
    inference(resolution,[status(thm)],[c_6,c_1619])).

tff(c_134,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95),B_95)
      | r1_xboole_0(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_602,plain,(
    ! [A_132,B_133,A_134] :
      ( ~ r1_xboole_0(A_132,B_133)
      | r1_xboole_0(A_134,k3_xboole_0(A_132,B_133)) ) ),
    inference(resolution,[status(thm)],[c_134,c_10])).

tff(c_947,plain,(
    ! [A_150,A_151,B_152] :
      ( k4_xboole_0(A_150,k3_xboole_0(A_151,B_152)) = A_150
      | ~ r1_xboole_0(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_602,c_18])).

tff(c_966,plain,(
    ! [A_151,B_152] :
      ( k3_xboole_0(A_151,B_152) = k1_xboole_0
      | ~ r1_xboole_0(A_151,B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_184])).

tff(c_1896,plain,(
    ! [B_202] : k3_xboole_0(k10_relat_1('#skF_12','#skF_11'),B_202) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1682,c_966])).

tff(c_185,plain,(
    ! [A_99] : k4_xboole_0(A_99,A_99) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_190,plain,(
    ! [A_99] : k4_xboole_0(A_99,k1_xboole_0) = k3_xboole_0(A_99,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_16])).

tff(c_208,plain,(
    ! [A_99] : k3_xboole_0(A_99,A_99) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_190])).

tff(c_1932,plain,(
    k10_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_208])).

tff(c_1973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1932])).

tff(c_1975,plain,(
    ! [A_203] : ~ r1_xboole_0(A_203,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1979,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) != A_15 ),
    inference(resolution,[status(thm)],[c_20,c_1975])).

tff(c_1983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1979])).

tff(c_1984,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2056,plain,(
    ! [A_210,B_211,C_212] :
      ( ~ r1_xboole_0(A_210,B_211)
      | ~ r2_hidden(C_212,k3_xboole_0(A_210,B_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2066,plain,(
    ! [A_11,C_212] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_212,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2056])).

tff(c_2068,plain,(
    ! [C_212] : ~ r2_hidden(C_212,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2066])).

tff(c_1985,plain,(
    k10_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_40,plain,(
    ! [A_59,C_74] :
      ( r2_hidden(k4_tarski('#skF_10'(A_59,k2_relat_1(A_59),C_74),C_74),A_59)
      | ~ r2_hidden(C_74,k2_relat_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2869,plain,(
    ! [D_277,A_278,B_279,E_280] :
      ( r2_hidden(D_277,k10_relat_1(A_278,B_279))
      | ~ r2_hidden(E_280,B_279)
      | ~ r2_hidden(k4_tarski(D_277,E_280),A_278)
      | ~ v1_relat_1(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9905,plain,(
    ! [D_477,A_478,B_479,A_480] :
      ( r2_hidden(D_477,k10_relat_1(A_478,B_479))
      | ~ r2_hidden(k4_tarski(D_477,'#skF_1'(A_480,B_479)),A_478)
      | ~ v1_relat_1(A_478)
      | r1_xboole_0(A_480,B_479) ) ),
    inference(resolution,[status(thm)],[c_4,c_2869])).

tff(c_147933,plain,(
    ! [A_18890,A_18891,B_18892] :
      ( r2_hidden('#skF_10'(A_18890,k2_relat_1(A_18890),'#skF_1'(A_18891,B_18892)),k10_relat_1(A_18890,B_18892))
      | ~ v1_relat_1(A_18890)
      | r1_xboole_0(A_18891,B_18892)
      | ~ r2_hidden('#skF_1'(A_18891,B_18892),k2_relat_1(A_18890)) ) ),
    inference(resolution,[status(thm)],[c_40,c_9905])).

tff(c_148368,plain,(
    ! [A_18891] :
      ( r2_hidden('#skF_10'('#skF_12',k2_relat_1('#skF_12'),'#skF_1'(A_18891,'#skF_11')),k1_xboole_0)
      | ~ v1_relat_1('#skF_12')
      | r1_xboole_0(A_18891,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_18891,'#skF_11'),k2_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1985,c_147933])).

tff(c_148487,plain,(
    ! [A_18891] :
      ( r2_hidden('#skF_10'('#skF_12',k2_relat_1('#skF_12'),'#skF_1'(A_18891,'#skF_11')),k1_xboole_0)
      | r1_xboole_0(A_18891,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_18891,'#skF_11'),k2_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_148368])).

tff(c_150320,plain,(
    ! [A_19333] :
      ( r1_xboole_0(A_19333,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_19333,'#skF_11'),k2_relat_1('#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2068,c_148487])).

tff(c_150336,plain,(
    r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_150320])).

tff(c_150340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1984,c_1984,c_150336])).

tff(c_150342,plain,(
    ! [A_19369] : ~ r1_xboole_0(A_19369,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2066])).

tff(c_150346,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) != A_15 ),
    inference(resolution,[status(thm)],[c_20,c_150342])).

tff(c_150350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.60/28.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.60/28.27  
% 37.60/28.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.60/28.27  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10
% 37.60/28.27  
% 37.60/28.27  %Foreground sorts:
% 37.60/28.27  
% 37.60/28.27  
% 37.60/28.27  %Background operators:
% 37.60/28.27  
% 37.60/28.27  
% 37.60/28.27  %Foreground operators:
% 37.60/28.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.60/28.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.60/28.27  tff('#skF_11', type, '#skF_11': $i).
% 37.60/28.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 37.60/28.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 37.60/28.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.60/28.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 37.60/28.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 37.60/28.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 37.60/28.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 37.60/28.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 37.60/28.27  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 37.60/28.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.60/28.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 37.60/28.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 37.60/28.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 37.60/28.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.60/28.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 37.60/28.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 37.60/28.27  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 37.60/28.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 37.60/28.27  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 37.60/28.27  tff('#skF_12', type, '#skF_12': $i).
% 37.60/28.27  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 37.60/28.27  
% 37.60/28.29  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 37.60/28.29  tff(f_67, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 37.60/28.29  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 37.60/28.29  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 37.60/28.29  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 37.60/28.29  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 37.60/28.29  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 37.60/28.29  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 37.60/28.29  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 37.60/28.29  tff(f_88, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 37.60/28.29  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 37.60/28.29  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_67])).
% 37.60/28.29  tff(c_56, plain, (~r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11') | k10_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.60/28.29  tff(c_85, plain, (k10_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 37.60/28.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 37.60/28.29  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 37.60/28.29  tff(c_87, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, k3_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 37.60/28.29  tff(c_94, plain, (![A_11, C_90]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_87])).
% 37.60/28.29  tff(c_101, plain, (![C_90]: (~r2_hidden(C_90, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_94])).
% 37.60/28.29  tff(c_54, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.60/28.29  tff(c_151, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k4_xboole_0(A_97, B_98))=k3_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 37.60/28.29  tff(c_180, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_151])).
% 37.60/28.29  tff(c_184, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_180])).
% 37.60/28.29  tff(c_62, plain, (k10_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.60/28.29  tff(c_96, plain, (r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_85, c_62])).
% 37.60/28.29  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 37.60/28.29  tff(c_100, plain, (k4_xboole_0(k2_relat_1('#skF_12'), '#skF_11')=k2_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_96, c_18])).
% 37.60/28.29  tff(c_170, plain, (k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_12'))=k3_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_100, c_151])).
% 37.60/28.29  tff(c_214, plain, (k3_xboole_0(k2_relat_1('#skF_12'), '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_184, c_170])).
% 37.60/28.29  tff(c_739, plain, (![B_143, A_144]: (k10_relat_1(B_143, k3_xboole_0(k2_relat_1(B_143), A_144))=k10_relat_1(B_143, A_144) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_92])).
% 37.60/28.29  tff(c_764, plain, (k10_relat_1('#skF_12', k1_xboole_0)=k10_relat_1('#skF_12', '#skF_11') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_214, c_739])).
% 37.60/28.29  tff(c_769, plain, (k10_relat_1('#skF_12', k1_xboole_0)=k10_relat_1('#skF_12', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_764])).
% 37.60/28.29  tff(c_1587, plain, (![A_184, B_185, D_186]: (r2_hidden('#skF_6'(A_184, B_185, k10_relat_1(A_184, B_185), D_186), B_185) | ~r2_hidden(D_186, k10_relat_1(A_184, B_185)) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_80])).
% 37.60/28.29  tff(c_1607, plain, (![D_186]: (r2_hidden('#skF_6'('#skF_12', k1_xboole_0, k10_relat_1('#skF_12', '#skF_11'), D_186), k1_xboole_0) | ~r2_hidden(D_186, k10_relat_1('#skF_12', k1_xboole_0)) | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_769, c_1587])).
% 37.60/28.29  tff(c_1617, plain, (![D_186]: (r2_hidden('#skF_6'('#skF_12', k1_xboole_0, k10_relat_1('#skF_12', '#skF_11'), D_186), k1_xboole_0) | ~r2_hidden(D_186, k10_relat_1('#skF_12', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_769, c_1607])).
% 37.60/28.29  tff(c_1619, plain, (![D_187]: (~r2_hidden(D_187, k10_relat_1('#skF_12', '#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_101, c_1617])).
% 37.60/28.29  tff(c_1682, plain, (![B_191]: (r1_xboole_0(k10_relat_1('#skF_12', '#skF_11'), B_191))), inference(resolution, [status(thm)], [c_6, c_1619])).
% 37.60/28.29  tff(c_134, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95), B_95) | r1_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 37.60/28.29  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 37.60/28.29  tff(c_602, plain, (![A_132, B_133, A_134]: (~r1_xboole_0(A_132, B_133) | r1_xboole_0(A_134, k3_xboole_0(A_132, B_133)))), inference(resolution, [status(thm)], [c_134, c_10])).
% 37.60/28.29  tff(c_947, plain, (![A_150, A_151, B_152]: (k4_xboole_0(A_150, k3_xboole_0(A_151, B_152))=A_150 | ~r1_xboole_0(A_151, B_152))), inference(resolution, [status(thm)], [c_602, c_18])).
% 37.60/28.29  tff(c_966, plain, (![A_151, B_152]: (k3_xboole_0(A_151, B_152)=k1_xboole_0 | ~r1_xboole_0(A_151, B_152))), inference(superposition, [status(thm), theory('equality')], [c_947, c_184])).
% 37.60/28.29  tff(c_1896, plain, (![B_202]: (k3_xboole_0(k10_relat_1('#skF_12', '#skF_11'), B_202)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1682, c_966])).
% 37.60/28.29  tff(c_185, plain, (![A_99]: (k4_xboole_0(A_99, A_99)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_180])).
% 37.60/28.29  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 37.60/28.29  tff(c_190, plain, (![A_99]: (k4_xboole_0(A_99, k1_xboole_0)=k3_xboole_0(A_99, A_99))), inference(superposition, [status(thm), theory('equality')], [c_185, c_16])).
% 37.60/28.29  tff(c_208, plain, (![A_99]: (k3_xboole_0(A_99, A_99)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_190])).
% 37.60/28.29  tff(c_1932, plain, (k10_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1896, c_208])).
% 37.60/28.29  tff(c_1973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_1932])).
% 37.60/28.29  tff(c_1975, plain, (![A_203]: (~r1_xboole_0(A_203, k1_xboole_0))), inference(splitRight, [status(thm)], [c_94])).
% 37.60/28.29  tff(c_1979, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)!=A_15)), inference(resolution, [status(thm)], [c_20, c_1975])).
% 37.60/28.29  tff(c_1983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1979])).
% 37.60/28.29  tff(c_1984, plain, (~r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(splitRight, [status(thm)], [c_56])).
% 37.60/28.29  tff(c_2056, plain, (![A_210, B_211, C_212]: (~r1_xboole_0(A_210, B_211) | ~r2_hidden(C_212, k3_xboole_0(A_210, B_211)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 37.60/28.29  tff(c_2066, plain, (![A_11, C_212]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_212, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2056])).
% 37.60/28.29  tff(c_2068, plain, (![C_212]: (~r2_hidden(C_212, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2066])).
% 37.60/28.29  tff(c_1985, plain, (k10_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 37.60/28.29  tff(c_40, plain, (![A_59, C_74]: (r2_hidden(k4_tarski('#skF_10'(A_59, k2_relat_1(A_59), C_74), C_74), A_59) | ~r2_hidden(C_74, k2_relat_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 37.60/28.29  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 37.60/28.29  tff(c_2869, plain, (![D_277, A_278, B_279, E_280]: (r2_hidden(D_277, k10_relat_1(A_278, B_279)) | ~r2_hidden(E_280, B_279) | ~r2_hidden(k4_tarski(D_277, E_280), A_278) | ~v1_relat_1(A_278))), inference(cnfTransformation, [status(thm)], [f_80])).
% 37.60/28.29  tff(c_9905, plain, (![D_477, A_478, B_479, A_480]: (r2_hidden(D_477, k10_relat_1(A_478, B_479)) | ~r2_hidden(k4_tarski(D_477, '#skF_1'(A_480, B_479)), A_478) | ~v1_relat_1(A_478) | r1_xboole_0(A_480, B_479))), inference(resolution, [status(thm)], [c_4, c_2869])).
% 37.60/28.29  tff(c_147933, plain, (![A_18890, A_18891, B_18892]: (r2_hidden('#skF_10'(A_18890, k2_relat_1(A_18890), '#skF_1'(A_18891, B_18892)), k10_relat_1(A_18890, B_18892)) | ~v1_relat_1(A_18890) | r1_xboole_0(A_18891, B_18892) | ~r2_hidden('#skF_1'(A_18891, B_18892), k2_relat_1(A_18890)))), inference(resolution, [status(thm)], [c_40, c_9905])).
% 37.60/28.29  tff(c_148368, plain, (![A_18891]: (r2_hidden('#skF_10'('#skF_12', k2_relat_1('#skF_12'), '#skF_1'(A_18891, '#skF_11')), k1_xboole_0) | ~v1_relat_1('#skF_12') | r1_xboole_0(A_18891, '#skF_11') | ~r2_hidden('#skF_1'(A_18891, '#skF_11'), k2_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_1985, c_147933])).
% 37.60/28.29  tff(c_148487, plain, (![A_18891]: (r2_hidden('#skF_10'('#skF_12', k2_relat_1('#skF_12'), '#skF_1'(A_18891, '#skF_11')), k1_xboole_0) | r1_xboole_0(A_18891, '#skF_11') | ~r2_hidden('#skF_1'(A_18891, '#skF_11'), k2_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_148368])).
% 37.60/28.29  tff(c_150320, plain, (![A_19333]: (r1_xboole_0(A_19333, '#skF_11') | ~r2_hidden('#skF_1'(A_19333, '#skF_11'), k2_relat_1('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_2068, c_148487])).
% 37.60/28.29  tff(c_150336, plain, (r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_6, c_150320])).
% 37.60/28.29  tff(c_150340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1984, c_1984, c_150336])).
% 37.60/28.29  tff(c_150342, plain, (![A_19369]: (~r1_xboole_0(A_19369, k1_xboole_0))), inference(splitRight, [status(thm)], [c_2066])).
% 37.60/28.29  tff(c_150346, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)!=A_15)), inference(resolution, [status(thm)], [c_20, c_150342])).
% 37.60/28.29  tff(c_150350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_150346])).
% 37.60/28.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.60/28.29  
% 37.60/28.29  Inference rules
% 37.60/28.29  ----------------------
% 37.60/28.29  #Ref     : 5
% 37.60/28.29  #Sup     : 37681
% 37.60/28.29  #Fact    : 0
% 37.60/28.29  #Define  : 0
% 37.60/28.29  #Split   : 12
% 37.60/28.29  #Chain   : 0
% 37.60/28.29  #Close   : 0
% 37.60/28.29  
% 37.60/28.29  Ordering : KBO
% 37.60/28.29  
% 37.60/28.29  Simplification rules
% 37.60/28.29  ----------------------
% 37.60/28.29  #Subsume      : 16149
% 37.60/28.29  #Demod        : 18885
% 37.60/28.29  #Tautology    : 8338
% 37.60/28.29  #SimpNegUnit  : 700
% 37.60/28.29  #BackRed      : 109
% 37.60/28.29  
% 37.60/28.29  #Partial instantiations: 9198
% 37.60/28.29  #Strategies tried      : 1
% 37.60/28.29  
% 37.60/28.29  Timing (in seconds)
% 37.60/28.29  ----------------------
% 37.60/28.29  Preprocessing        : 0.31
% 37.60/28.29  Parsing              : 0.16
% 37.60/28.29  CNF conversion       : 0.03
% 37.60/28.29  Main loop            : 27.22
% 37.60/28.29  Inferencing          : 2.57
% 37.60/28.29  Reduction            : 8.66
% 37.60/28.29  Demodulation         : 7.00
% 37.60/28.29  BG Simplification    : 0.30
% 37.60/28.29  Subsumption          : 14.50
% 37.60/28.29  Abstraction          : 0.52
% 37.60/28.29  MUC search           : 0.00
% 37.60/28.29  Cooper               : 0.00
% 37.60/28.29  Total                : 27.56
% 37.60/28.29  Index Insertion      : 0.00
% 37.60/28.29  Index Deletion       : 0.00
% 37.60/28.29  Index Matching       : 0.00
% 37.60/28.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
