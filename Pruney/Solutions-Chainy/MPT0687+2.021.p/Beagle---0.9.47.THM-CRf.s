%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 16.61s
% Output     : CNFRefutation 16.61s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 149 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 ( 220 expanded)
%              Number of equality atoms :   63 (  95 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_101,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_149,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_58])).

tff(c_75,plain,(
    ! [A_40] :
      ( k10_relat_1(A_40,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_79,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_75])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_144,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148,plain,(
    ! [A_10,B_11] : k4_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_144])).

tff(c_130,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_12,c_130])).

tff(c_171,plain,(
    ! [A_60,B_61] : k4_xboole_0(k2_xboole_0(A_60,B_61),B_61) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_184,plain,(
    ! [A_10,B_11] : k4_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_171])).

tff(c_187,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_184])).

tff(c_338,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,k1_tarski(B_72)) = A_71
      | r2_hidden(B_72,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_344,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,A_71) = k3_xboole_0(A_71,k1_tarski(B_72))
      | r2_hidden(B_72,A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_20])).

tff(c_1267,plain,(
    ! [A_119,B_120] :
      ( k3_xboole_0(A_119,k1_tarski(B_120)) = k1_xboole_0
      | r2_hidden(B_120,A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_344])).

tff(c_36,plain,(
    ! [B_29,A_28] :
      ( k10_relat_1(B_29,k3_xboole_0(k2_relat_1(B_29),A_28)) = k10_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36636,plain,(
    ! [B_552,B_553] :
      ( k10_relat_1(B_552,k1_tarski(B_553)) = k10_relat_1(B_552,k1_xboole_0)
      | ~ v1_relat_1(B_552)
      | r2_hidden(B_553,k2_relat_1(B_552)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1267,c_36])).

tff(c_36642,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k10_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36636,c_101])).

tff(c_36649,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_79,c_36642])).

tff(c_36651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_36649])).

tff(c_36652,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_36653,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_92,plain,(
    ! [A_43] :
      ( k7_relat_1(A_43,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_100,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_92])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k7_relat_1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36657,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_30])).

tff(c_36661,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36657])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_27] : k7_relat_1(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36794,plain,(
    ! [B_579,A_580] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_579,A_580)),A_580)
      | ~ v1_relat_1(B_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36806,plain,(
    ! [A_27] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_27)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_36794])).

tff(c_36823,plain,(
    ! [A_581] : r1_tarski(k1_xboole_0,A_581) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36661,c_44,c_36806])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36882,plain,(
    ! [A_585] : k4_xboole_0(k1_xboole_0,A_585) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36823,c_16])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( ~ r2_hidden(B_23,A_22)
      | k4_xboole_0(A_22,k1_tarski(B_23)) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36919,plain,(
    ! [B_23] : ~ r2_hidden(B_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36882,c_26])).

tff(c_36687,plain,(
    ! [A_558,B_559] :
      ( k4_xboole_0(A_558,B_559) = k1_xboole_0
      | ~ r1_tarski(A_558,B_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36691,plain,(
    ! [A_10,B_11] : k4_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_36687])).

tff(c_36704,plain,(
    ! [A_564,B_565] :
      ( k2_xboole_0(A_564,B_565) = B_565
      | ~ r1_tarski(A_564,B_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36712,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_12,c_36704])).

tff(c_36749,plain,(
    ! [A_575,B_576] : k4_xboole_0(k2_xboole_0(A_575,B_576),B_576) = k4_xboole_0(A_575,B_576) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36770,plain,(
    ! [A_10,B_11] : k4_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_36712,c_36749])).

tff(c_36773,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36691,c_36770])).

tff(c_36887,plain,(
    ! [A_585] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,A_585) ),
    inference(superposition,[status(thm),theory(equality)],[c_36882,c_20])).

tff(c_36917,plain,(
    ! [A_585] : k3_xboole_0(k1_xboole_0,A_585) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36773,c_36887])).

tff(c_37039,plain,(
    ! [B_591,A_592] :
      ( r2_hidden(B_591,A_592)
      | k3_xboole_0(A_592,k1_tarski(B_591)) != k1_tarski(B_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_37050,plain,(
    ! [B_591] :
      ( r2_hidden(B_591,k1_xboole_0)
      | k1_tarski(B_591) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36917,c_37039])).

tff(c_37052,plain,(
    ! [B_591] : k1_tarski(B_591) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36919,c_37050])).

tff(c_36948,plain,(
    ! [B_588,A_589] :
      ( k3_xboole_0(B_588,k1_tarski(A_589)) = k1_tarski(A_589)
      | ~ r2_hidden(A_589,B_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36967,plain,(
    ! [A_589,B_588] :
      ( r1_tarski(k1_tarski(A_589),B_588)
      | ~ r2_hidden(A_589,B_588) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36948,c_12])).

tff(c_37476,plain,(
    ! [B_615,A_616] :
      ( k10_relat_1(B_615,A_616) != k1_xboole_0
      | ~ r1_tarski(A_616,k2_relat_1(B_615))
      | k1_xboole_0 = A_616
      | ~ v1_relat_1(B_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_37480,plain,(
    ! [B_615,A_589] :
      ( k10_relat_1(B_615,k1_tarski(A_589)) != k1_xboole_0
      | k1_tarski(A_589) = k1_xboole_0
      | ~ v1_relat_1(B_615)
      | ~ r2_hidden(A_589,k2_relat_1(B_615)) ) ),
    inference(resolution,[status(thm)],[c_36967,c_37476])).

tff(c_44109,plain,(
    ! [B_745,A_746] :
      ( k10_relat_1(B_745,k1_tarski(A_746)) != k1_xboole_0
      | ~ v1_relat_1(B_745)
      | ~ r2_hidden(A_746,k2_relat_1(B_745)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37052,c_37480])).

tff(c_44112,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36653,c_44109])).

tff(c_44119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36652,c_44112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:01:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.61/8.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.61/8.34  
% 16.61/8.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.61/8.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 16.61/8.34  
% 16.61/8.34  %Foreground sorts:
% 16.61/8.34  
% 16.61/8.34  
% 16.61/8.34  %Background operators:
% 16.61/8.34  
% 16.61/8.34  
% 16.61/8.34  %Foreground operators:
% 16.61/8.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.61/8.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.61/8.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.61/8.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.61/8.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.61/8.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.61/8.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.61/8.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.61/8.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.61/8.34  tff('#skF_2', type, '#skF_2': $i).
% 16.61/8.34  tff('#skF_3', type, '#skF_3': $i).
% 16.61/8.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.61/8.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 16.61/8.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.61/8.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.61/8.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.61/8.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.61/8.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.61/8.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.61/8.34  
% 16.61/8.36  tff(f_117, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 16.61/8.36  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 16.61/8.36  tff(f_49, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 16.61/8.36  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 16.61/8.36  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.61/8.36  tff(f_55, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 16.61/8.36  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 16.61/8.36  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.61/8.36  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 16.61/8.36  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 16.61/8.36  tff(f_74, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 16.61/8.36  tff(f_101, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 16.61/8.36  tff(f_80, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 16.61/8.36  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 16.61/8.36  tff(f_61, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 16.61/8.36  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 16.61/8.36  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 16.61/8.36  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.61/8.36  tff(c_52, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.61/8.36  tff(c_101, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 16.61/8.36  tff(c_58, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.61/8.36  tff(c_149, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_101, c_58])).
% 16.61/8.36  tff(c_75, plain, (![A_40]: (k10_relat_1(A_40, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.61/8.36  tff(c_79, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_75])).
% 16.61/8.36  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.61/8.36  tff(c_144, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.61/8.36  tff(c_148, plain, (![A_10, B_11]: (k4_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_144])).
% 16.61/8.36  tff(c_130, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.61/8.36  tff(c_134, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_12, c_130])).
% 16.61/8.36  tff(c_171, plain, (![A_60, B_61]: (k4_xboole_0(k2_xboole_0(A_60, B_61), B_61)=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.61/8.36  tff(c_184, plain, (![A_10, B_11]: (k4_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_134, c_171])).
% 16.61/8.36  tff(c_187, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_184])).
% 16.61/8.36  tff(c_338, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k1_tarski(B_72))=A_71 | r2_hidden(B_72, A_71))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.61/8.36  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.61/8.36  tff(c_344, plain, (![A_71, B_72]: (k4_xboole_0(A_71, A_71)=k3_xboole_0(A_71, k1_tarski(B_72)) | r2_hidden(B_72, A_71))), inference(superposition, [status(thm), theory('equality')], [c_338, c_20])).
% 16.61/8.36  tff(c_1267, plain, (![A_119, B_120]: (k3_xboole_0(A_119, k1_tarski(B_120))=k1_xboole_0 | r2_hidden(B_120, A_119))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_344])).
% 16.61/8.36  tff(c_36, plain, (![B_29, A_28]: (k10_relat_1(B_29, k3_xboole_0(k2_relat_1(B_29), A_28))=k10_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.61/8.36  tff(c_36636, plain, (![B_552, B_553]: (k10_relat_1(B_552, k1_tarski(B_553))=k10_relat_1(B_552, k1_xboole_0) | ~v1_relat_1(B_552) | r2_hidden(B_553, k2_relat_1(B_552)))), inference(superposition, [status(thm), theory('equality')], [c_1267, c_36])).
% 16.61/8.36  tff(c_36642, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k10_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36636, c_101])).
% 16.61/8.36  tff(c_36649, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_79, c_36642])).
% 16.61/8.36  tff(c_36651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_36649])).
% 16.61/8.36  tff(c_36652, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 16.61/8.36  tff(c_36653, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 16.61/8.36  tff(c_92, plain, (![A_43]: (k7_relat_1(A_43, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.61/8.36  tff(c_100, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_92])).
% 16.61/8.36  tff(c_30, plain, (![A_24, B_25]: (v1_relat_1(k7_relat_1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.61/8.36  tff(c_36657, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_100, c_30])).
% 16.61/8.36  tff(c_36661, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36657])).
% 16.61/8.36  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.61/8.36  tff(c_34, plain, (![A_27]: (k7_relat_1(k1_xboole_0, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.61/8.36  tff(c_36794, plain, (![B_579, A_580]: (r1_tarski(k1_relat_1(k7_relat_1(B_579, A_580)), A_580) | ~v1_relat_1(B_579))), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.61/8.36  tff(c_36806, plain, (![A_27]: (r1_tarski(k1_relat_1(k1_xboole_0), A_27) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_36794])).
% 16.61/8.36  tff(c_36823, plain, (![A_581]: (r1_tarski(k1_xboole_0, A_581))), inference(demodulation, [status(thm), theory('equality')], [c_36661, c_44, c_36806])).
% 16.61/8.36  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.61/8.36  tff(c_36882, plain, (![A_585]: (k4_xboole_0(k1_xboole_0, A_585)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36823, c_16])).
% 16.61/8.36  tff(c_26, plain, (![B_23, A_22]: (~r2_hidden(B_23, A_22) | k4_xboole_0(A_22, k1_tarski(B_23))!=A_22)), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.61/8.36  tff(c_36919, plain, (![B_23]: (~r2_hidden(B_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36882, c_26])).
% 16.61/8.36  tff(c_36687, plain, (![A_558, B_559]: (k4_xboole_0(A_558, B_559)=k1_xboole_0 | ~r1_tarski(A_558, B_559))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.61/8.36  tff(c_36691, plain, (![A_10, B_11]: (k4_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_36687])).
% 16.61/8.36  tff(c_36704, plain, (![A_564, B_565]: (k2_xboole_0(A_564, B_565)=B_565 | ~r1_tarski(A_564, B_565))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.61/8.36  tff(c_36712, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_12, c_36704])).
% 16.61/8.36  tff(c_36749, plain, (![A_575, B_576]: (k4_xboole_0(k2_xboole_0(A_575, B_576), B_576)=k4_xboole_0(A_575, B_576))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.61/8.36  tff(c_36770, plain, (![A_10, B_11]: (k4_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_36712, c_36749])).
% 16.61/8.36  tff(c_36773, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36691, c_36770])).
% 16.61/8.36  tff(c_36887, plain, (![A_585]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, A_585))), inference(superposition, [status(thm), theory('equality')], [c_36882, c_20])).
% 16.61/8.36  tff(c_36917, plain, (![A_585]: (k3_xboole_0(k1_xboole_0, A_585)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36773, c_36887])).
% 16.61/8.36  tff(c_37039, plain, (![B_591, A_592]: (r2_hidden(B_591, A_592) | k3_xboole_0(A_592, k1_tarski(B_591))!=k1_tarski(B_591))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.61/8.36  tff(c_37050, plain, (![B_591]: (r2_hidden(B_591, k1_xboole_0) | k1_tarski(B_591)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36917, c_37039])).
% 16.61/8.36  tff(c_37052, plain, (![B_591]: (k1_tarski(B_591)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_36919, c_37050])).
% 16.61/8.36  tff(c_36948, plain, (![B_588, A_589]: (k3_xboole_0(B_588, k1_tarski(A_589))=k1_tarski(A_589) | ~r2_hidden(A_589, B_588))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.61/8.36  tff(c_36967, plain, (![A_589, B_588]: (r1_tarski(k1_tarski(A_589), B_588) | ~r2_hidden(A_589, B_588))), inference(superposition, [status(thm), theory('equality')], [c_36948, c_12])).
% 16.61/8.36  tff(c_37476, plain, (![B_615, A_616]: (k10_relat_1(B_615, A_616)!=k1_xboole_0 | ~r1_tarski(A_616, k2_relat_1(B_615)) | k1_xboole_0=A_616 | ~v1_relat_1(B_615))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.61/8.36  tff(c_37480, plain, (![B_615, A_589]: (k10_relat_1(B_615, k1_tarski(A_589))!=k1_xboole_0 | k1_tarski(A_589)=k1_xboole_0 | ~v1_relat_1(B_615) | ~r2_hidden(A_589, k2_relat_1(B_615)))), inference(resolution, [status(thm)], [c_36967, c_37476])).
% 16.61/8.36  tff(c_44109, plain, (![B_745, A_746]: (k10_relat_1(B_745, k1_tarski(A_746))!=k1_xboole_0 | ~v1_relat_1(B_745) | ~r2_hidden(A_746, k2_relat_1(B_745)))), inference(negUnitSimplification, [status(thm)], [c_37052, c_37480])).
% 16.61/8.36  tff(c_44112, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36653, c_44109])).
% 16.61/8.36  tff(c_44119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_36652, c_44112])).
% 16.61/8.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.61/8.36  
% 16.61/8.36  Inference rules
% 16.61/8.36  ----------------------
% 16.61/8.36  #Ref     : 0
% 16.61/8.36  #Sup     : 10172
% 16.61/8.36  #Fact    : 2
% 16.61/8.36  #Define  : 0
% 16.61/8.36  #Split   : 8
% 16.61/8.36  #Chain   : 0
% 16.61/8.36  #Close   : 0
% 16.61/8.36  
% 16.61/8.36  Ordering : KBO
% 16.61/8.36  
% 16.61/8.36  Simplification rules
% 16.61/8.36  ----------------------
% 16.61/8.36  #Subsume      : 2340
% 16.61/8.36  #Demod        : 15395
% 16.61/8.36  #Tautology    : 4039
% 16.61/8.36  #SimpNegUnit  : 560
% 16.61/8.36  #BackRed      : 11
% 16.61/8.36  
% 16.61/8.36  #Partial instantiations: 0
% 16.61/8.36  #Strategies tried      : 1
% 16.61/8.36  
% 16.61/8.36  Timing (in seconds)
% 16.61/8.36  ----------------------
% 16.61/8.36  Preprocessing        : 0.33
% 16.61/8.36  Parsing              : 0.18
% 16.61/8.36  CNF conversion       : 0.02
% 16.61/8.36  Main loop            : 7.26
% 16.61/8.36  Inferencing          : 1.24
% 16.61/8.37  Reduction            : 4.03
% 16.61/8.37  Demodulation         : 3.54
% 16.61/8.37  BG Simplification    : 0.14
% 16.61/8.37  Subsumption          : 1.56
% 16.61/8.37  Abstraction          : 0.23
% 16.61/8.37  MUC search           : 0.00
% 16.61/8.37  Cooper               : 0.00
% 16.61/8.37  Total                : 7.63
% 16.61/8.37  Index Insertion      : 0.00
% 16.61/8.37  Index Deletion       : 0.00
% 16.61/8.37  Index Matching       : 0.00
% 16.61/8.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
