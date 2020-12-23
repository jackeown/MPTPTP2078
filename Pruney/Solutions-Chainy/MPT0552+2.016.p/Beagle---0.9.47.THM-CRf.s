%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:59 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 165 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 353 expanded)
%              Number of equality atoms :    5 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k7_relat_1(B_24,A_23),B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_13,A_11),B_12) = k7_relat_1(C_13,k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_596,plain,(
    ! [B_133,A_134,C_135] :
      ( r1_tarski(k7_relat_1(B_133,A_134),k7_relat_1(C_135,A_134))
      | ~ r1_tarski(B_133,C_135)
      | ~ v1_relat_1(C_135)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_602,plain,(
    ! [C_13,A_11,B_12,C_135] :
      ( r1_tarski(k7_relat_1(C_13,k3_xboole_0(A_11,B_12)),k7_relat_1(C_135,B_12))
      | ~ r1_tarski(k7_relat_1(C_13,A_11),C_135)
      | ~ v1_relat_1(C_135)
      | ~ v1_relat_1(k7_relat_1(C_13,A_11))
      | ~ v1_relat_1(C_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_596])).

tff(c_16,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k2_relat_1(A_52),k2_relat_1(B_53))
      | ~ r1_tarski(A_52,B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_740,plain,(
    ! [B_159,A_160,B_161] :
      ( r1_tarski(k9_relat_1(B_159,A_160),k2_relat_1(B_161))
      | ~ r1_tarski(k7_relat_1(B_159,A_160),B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(k7_relat_1(B_159,A_160))
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_89])).

tff(c_2338,plain,(
    ! [B_301,A_302,B_303,A_304] :
      ( r1_tarski(k9_relat_1(B_301,A_302),k9_relat_1(B_303,A_304))
      | ~ r1_tarski(k7_relat_1(B_301,A_302),k7_relat_1(B_303,A_304))
      | ~ v1_relat_1(k7_relat_1(B_303,A_304))
      | ~ v1_relat_1(k7_relat_1(B_301,A_302))
      | ~ v1_relat_1(B_301)
      | ~ v1_relat_1(B_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_740])).

tff(c_100,plain,(
    ! [C_54,A_55,B_56] :
      ( k7_relat_1(k7_relat_1(C_54,A_55),B_56) = k7_relat_1(C_54,k3_xboole_0(A_55,B_56))
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_26,A_25)),k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_182,plain,(
    ! [C_75,A_76,B_77] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_75,k3_xboole_0(A_76,B_77))),k2_relat_1(k7_relat_1(C_75,A_76)))
      | ~ v1_relat_1(k7_relat_1(C_75,A_76))
      | ~ v1_relat_1(C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_24])).

tff(c_373,plain,(
    ! [B_108,A_109,B_110] :
      ( r1_tarski(k9_relat_1(B_108,k3_xboole_0(A_109,B_110)),k2_relat_1(k7_relat_1(B_108,A_109)))
      | ~ v1_relat_1(k7_relat_1(B_108,A_109))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_182])).

tff(c_558,plain,(
    ! [B_130,A_131,B_132] :
      ( r1_tarski(k9_relat_1(B_130,k3_xboole_0(A_131,B_132)),k9_relat_1(B_130,A_131))
      | ~ v1_relat_1(k7_relat_1(B_130,A_131))
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_373])).

tff(c_80,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(A_49,k3_xboole_0(B_50,C_51))
      | ~ r1_tarski(A_49,C_51)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_87,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_26])).

tff(c_142,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_561,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_558,c_142])).

tff(c_574,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_561])).

tff(c_578,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_574])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_578])).

tff(c_583,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_2343,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2338,c_583])).

tff(c_2374,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2343])).

tff(c_2376,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2374])).

tff(c_2379,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_2376])).

tff(c_2383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2379])).

tff(c_2384,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2374])).

tff(c_2386,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2384])).

tff(c_2389,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_602,c_2386])).

tff(c_2392,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2389])).

tff(c_2393,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2392])).

tff(c_2396,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_2393])).

tff(c_2400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2396])).

tff(c_2401,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2392])).

tff(c_2405,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2401])).

tff(c_2409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2405])).

tff(c_2410,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2384])).

tff(c_2484,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_2410])).

tff(c_2488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.95  
% 5.05/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.96  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.05/1.96  
% 5.05/1.96  %Foreground sorts:
% 5.05/1.96  
% 5.05/1.96  
% 5.05/1.96  %Background operators:
% 5.05/1.96  
% 5.05/1.96  
% 5.05/1.96  %Foreground operators:
% 5.05/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.05/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.05/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.05/1.96  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.05/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.05/1.96  tff('#skF_1', type, '#skF_1': $i).
% 5.05/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.05/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.05/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.05/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.05/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.05/1.96  
% 5.05/1.97  tff(f_87, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 5.05/1.97  tff(f_46, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.05/1.97  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 5.05/1.97  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 5.05/1.97  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 5.05/1.97  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.05/1.97  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.05/1.97  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 5.05/1.97  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.05/1.97  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.05/1.97  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.05/1.97  tff(c_22, plain, (![B_24, A_23]: (r1_tarski(k7_relat_1(B_24, A_23), B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.05/1.97  tff(c_12, plain, (![C_13, A_11, B_12]: (k7_relat_1(k7_relat_1(C_13, A_11), B_12)=k7_relat_1(C_13, k3_xboole_0(A_11, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.05/1.97  tff(c_596, plain, (![B_133, A_134, C_135]: (r1_tarski(k7_relat_1(B_133, A_134), k7_relat_1(C_135, A_134)) | ~r1_tarski(B_133, C_135) | ~v1_relat_1(C_135) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.05/1.97  tff(c_602, plain, (![C_13, A_11, B_12, C_135]: (r1_tarski(k7_relat_1(C_13, k3_xboole_0(A_11, B_12)), k7_relat_1(C_135, B_12)) | ~r1_tarski(k7_relat_1(C_13, A_11), C_135) | ~v1_relat_1(C_135) | ~v1_relat_1(k7_relat_1(C_13, A_11)) | ~v1_relat_1(C_13))), inference(superposition, [status(thm), theory('equality')], [c_12, c_596])).
% 5.05/1.97  tff(c_16, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.05/1.97  tff(c_89, plain, (![A_52, B_53]: (r1_tarski(k2_relat_1(A_52), k2_relat_1(B_53)) | ~r1_tarski(A_52, B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.05/1.97  tff(c_740, plain, (![B_159, A_160, B_161]: (r1_tarski(k9_relat_1(B_159, A_160), k2_relat_1(B_161)) | ~r1_tarski(k7_relat_1(B_159, A_160), B_161) | ~v1_relat_1(B_161) | ~v1_relat_1(k7_relat_1(B_159, A_160)) | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_16, c_89])).
% 5.05/1.97  tff(c_2338, plain, (![B_301, A_302, B_303, A_304]: (r1_tarski(k9_relat_1(B_301, A_302), k9_relat_1(B_303, A_304)) | ~r1_tarski(k7_relat_1(B_301, A_302), k7_relat_1(B_303, A_304)) | ~v1_relat_1(k7_relat_1(B_303, A_304)) | ~v1_relat_1(k7_relat_1(B_301, A_302)) | ~v1_relat_1(B_301) | ~v1_relat_1(B_303))), inference(superposition, [status(thm), theory('equality')], [c_16, c_740])).
% 5.05/1.97  tff(c_100, plain, (![C_54, A_55, B_56]: (k7_relat_1(k7_relat_1(C_54, A_55), B_56)=k7_relat_1(C_54, k3_xboole_0(A_55, B_56)) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.05/1.97  tff(c_24, plain, (![B_26, A_25]: (r1_tarski(k2_relat_1(k7_relat_1(B_26, A_25)), k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.05/1.97  tff(c_182, plain, (![C_75, A_76, B_77]: (r1_tarski(k2_relat_1(k7_relat_1(C_75, k3_xboole_0(A_76, B_77))), k2_relat_1(k7_relat_1(C_75, A_76))) | ~v1_relat_1(k7_relat_1(C_75, A_76)) | ~v1_relat_1(C_75))), inference(superposition, [status(thm), theory('equality')], [c_100, c_24])).
% 5.05/1.97  tff(c_373, plain, (![B_108, A_109, B_110]: (r1_tarski(k9_relat_1(B_108, k3_xboole_0(A_109, B_110)), k2_relat_1(k7_relat_1(B_108, A_109))) | ~v1_relat_1(k7_relat_1(B_108, A_109)) | ~v1_relat_1(B_108) | ~v1_relat_1(B_108))), inference(superposition, [status(thm), theory('equality')], [c_16, c_182])).
% 5.05/1.97  tff(c_558, plain, (![B_130, A_131, B_132]: (r1_tarski(k9_relat_1(B_130, k3_xboole_0(A_131, B_132)), k9_relat_1(B_130, A_131)) | ~v1_relat_1(k7_relat_1(B_130, A_131)) | ~v1_relat_1(B_130) | ~v1_relat_1(B_130) | ~v1_relat_1(B_130))), inference(superposition, [status(thm), theory('equality')], [c_16, c_373])).
% 5.05/1.97  tff(c_80, plain, (![A_49, B_50, C_51]: (r1_tarski(A_49, k3_xboole_0(B_50, C_51)) | ~r1_tarski(A_49, C_51) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.05/1.97  tff(c_26, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.05/1.97  tff(c_87, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_26])).
% 5.05/1.97  tff(c_142, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_87])).
% 5.05/1.97  tff(c_561, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_558, c_142])).
% 5.05/1.97  tff(c_574, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_561])).
% 5.05/1.97  tff(c_578, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_574])).
% 5.05/1.97  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_578])).
% 5.05/1.97  tff(c_583, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_87])).
% 5.05/1.97  tff(c_2343, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2338, c_583])).
% 5.05/1.97  tff(c_2374, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2343])).
% 5.05/1.97  tff(c_2376, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2374])).
% 5.05/1.97  tff(c_2379, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_2376])).
% 5.05/1.97  tff(c_2383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2379])).
% 5.05/1.97  tff(c_2384, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2374])).
% 5.05/1.97  tff(c_2386, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2384])).
% 5.05/1.97  tff(c_2389, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_602, c_2386])).
% 5.05/1.97  tff(c_2392, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2389])).
% 5.05/1.97  tff(c_2393, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2392])).
% 5.05/1.97  tff(c_2396, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_2393])).
% 5.05/1.97  tff(c_2400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2396])).
% 5.05/1.97  tff(c_2401, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_2392])).
% 5.05/1.97  tff(c_2405, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2401])).
% 5.05/1.97  tff(c_2409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2405])).
% 5.05/1.97  tff(c_2410, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2384])).
% 5.05/1.97  tff(c_2484, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_2410])).
% 5.05/1.97  tff(c_2488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2484])).
% 5.05/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.97  
% 5.05/1.97  Inference rules
% 5.05/1.97  ----------------------
% 5.05/1.97  #Ref     : 0
% 5.05/1.97  #Sup     : 702
% 5.05/1.97  #Fact    : 0
% 5.05/1.97  #Define  : 0
% 5.05/1.97  #Split   : 5
% 5.05/1.97  #Chain   : 0
% 5.05/1.97  #Close   : 0
% 5.05/1.97  
% 5.05/1.97  Ordering : KBO
% 5.05/1.97  
% 5.05/1.97  Simplification rules
% 5.05/1.97  ----------------------
% 5.05/1.97  #Subsume      : 103
% 5.05/1.97  #Demod        : 9
% 5.05/1.97  #Tautology    : 27
% 5.05/1.97  #SimpNegUnit  : 0
% 5.05/1.97  #BackRed      : 0
% 5.05/1.97  
% 5.05/1.97  #Partial instantiations: 0
% 5.05/1.97  #Strategies tried      : 1
% 5.05/1.97  
% 5.05/1.97  Timing (in seconds)
% 5.05/1.97  ----------------------
% 5.05/1.97  Preprocessing        : 0.26
% 5.05/1.97  Parsing              : 0.15
% 5.05/1.97  CNF conversion       : 0.02
% 5.05/1.97  Main loop            : 0.89
% 5.05/1.97  Inferencing          : 0.35
% 5.05/1.97  Reduction            : 0.19
% 5.05/1.97  Demodulation         : 0.13
% 5.05/1.97  BG Simplification    : 0.04
% 5.05/1.97  Subsumption          : 0.24
% 5.05/1.97  Abstraction          : 0.04
% 5.05/1.97  MUC search           : 0.00
% 5.05/1.97  Cooper               : 0.00
% 5.05/1.97  Total                : 1.18
% 5.05/1.97  Index Insertion      : 0.00
% 5.05/1.97  Index Deletion       : 0.00
% 5.05/1.97  Index Matching       : 0.00
% 5.05/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
