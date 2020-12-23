%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:13 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 180 expanded)
%              Number of leaves         :   37 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 257 expanded)
%              Number of equality atoms :   47 ( 125 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_96,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_94,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_109,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_308,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_317,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_308])).

tff(c_320,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_317])).

tff(c_70,plain,(
    ! [A_37] : k2_subset_1(A_37) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_82,plain,
    ( k2_subset_1('#skF_7') != '#skF_8'
    | ~ r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_90,plain,
    ( '#skF_7' != '#skF_8'
    | ~ r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_82])).

tff(c_138,plain,(
    ~ r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_88,plain,
    ( r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_8')
    | k2_subset_1('#skF_7') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_91,plain,
    ( r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_88])).

tff(c_161,plain,(
    '#skF_7' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_91])).

tff(c_80,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_163,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_80])).

tff(c_673,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(A_111,B_112) = k3_subset_1(A_111,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_686,plain,(
    k4_xboole_0('#skF_8','#skF_8') = k3_subset_1('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_163,c_673])).

tff(c_696,plain,(
    k3_subset_1('#skF_8','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_686])).

tff(c_162,plain,(
    ~ r1_tarski(k3_subset_1('#skF_8','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_138])).

tff(c_698,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_162])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_698])).

tff(c_702,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2192,plain,(
    ! [A_202,B_203] :
      ( k4_xboole_0(A_202,B_203) = k3_subset_1(A_202,B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(A_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2210,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_2192])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2399,plain,(
    ! [D_208] :
      ( r2_hidden(D_208,'#skF_7')
      | ~ r2_hidden(D_208,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2210,c_12])).

tff(c_2414,plain,
    ( r2_hidden('#skF_4'(k3_subset_1('#skF_7','#skF_8')),'#skF_7')
    | k3_subset_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_2399])).

tff(c_4544,plain,(
    k3_subset_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2414])).

tff(c_1960,plain,(
    ! [A_197,B_198] :
      ( k3_subset_1(A_197,k3_subset_1(A_197,B_198)) = B_198
      | ~ m1_subset_1(B_198,k1_zfmisc_1(A_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1974,plain,(
    k3_subset_1('#skF_7',k3_subset_1('#skF_7','#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_80,c_1960])).

tff(c_4557,plain,(
    k3_subset_1('#skF_7',k1_xboole_0) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_1974])).

tff(c_68,plain,(
    ! [A_36] : k1_subset_1(A_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_78,plain,(
    ! [A_43] : k3_subset_1(A_43,k1_subset_1(A_43)) = k2_subset_1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_89,plain,(
    ! [A_43] : k3_subset_1(A_43,k1_subset_1(A_43)) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_78])).

tff(c_92,plain,(
    ! [A_43] : k3_subset_1(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_89])).

tff(c_4619,plain,(
    '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4557,c_92])).

tff(c_4626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_702,c_4619])).

tff(c_4628,plain,(
    k3_subset_1('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2414])).

tff(c_703,plain,(
    r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_1593,plain,(
    ! [C_183,B_184,A_185] :
      ( r2_hidden(C_183,B_184)
      | ~ r2_hidden(C_183,A_185)
      | ~ r1_tarski(A_185,B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4629,plain,(
    ! [A_278,B_279] :
      ( r2_hidden('#skF_4'(A_278),B_279)
      | ~ r1_tarski(A_278,B_279)
      | k1_xboole_0 = A_278 ) ),
    inference(resolution,[status(thm)],[c_28,c_1593])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2770,plain,(
    ! [D_217] :
      ( ~ r2_hidden(D_217,'#skF_8')
      | ~ r2_hidden(D_217,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2210,c_10])).

tff(c_2785,plain,
    ( ~ r2_hidden('#skF_4'(k3_subset_1('#skF_7','#skF_8')),'#skF_8')
    | k3_subset_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_2770])).

tff(c_4389,plain,(
    ~ r2_hidden('#skF_4'(k3_subset_1('#skF_7','#skF_8')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2785])).

tff(c_4640,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_8')
    | k3_subset_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4629,c_4389])).

tff(c_4688,plain,(
    k3_subset_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_4640])).

tff(c_4702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4628,c_4688])).

tff(c_4703,plain,(
    k3_subset_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2785])).

tff(c_4715,plain,(
    k3_subset_1('#skF_7',k1_xboole_0) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4703,c_1974])).

tff(c_4757,plain,(
    '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4715,c_92])).

tff(c_4764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_702,c_4757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/2.03  
% 5.13/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/2.04  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 5.13/2.04  
% 5.13/2.04  %Foreground sorts:
% 5.13/2.04  
% 5.13/2.04  
% 5.13/2.04  %Background operators:
% 5.13/2.04  
% 5.13/2.04  
% 5.13/2.04  %Foreground operators:
% 5.13/2.04  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.13/2.04  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.13/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.13/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/2.04  tff('#skF_7', type, '#skF_7': $i).
% 5.13/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.13/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/2.04  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.13/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.13/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/2.04  tff('#skF_8', type, '#skF_8': $i).
% 5.13/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/2.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.13/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/2.04  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.13/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.13/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.13/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.13/2.04  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.13/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.13/2.04  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.13/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/2.04  
% 5.13/2.05  tff(f_66, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.13/2.05  tff(f_70, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.13/2.05  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.13/2.05  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.13/2.05  tff(f_96, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.13/2.05  tff(f_116, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 5.13/2.05  tff(f_100, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.13/2.05  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.13/2.05  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.13/2.05  tff(f_107, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.13/2.05  tff(f_94, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 5.13/2.05  tff(f_109, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 5.13/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.13/2.05  tff(c_40, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.13/2.05  tff(c_44, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.13/2.05  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.13/2.05  tff(c_308, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.13/2.05  tff(c_317, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_308])).
% 5.13/2.05  tff(c_320, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_317])).
% 5.13/2.05  tff(c_70, plain, (![A_37]: (k2_subset_1(A_37)=A_37)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.13/2.05  tff(c_82, plain, (k2_subset_1('#skF_7')!='#skF_8' | ~r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.13/2.05  tff(c_90, plain, ('#skF_7'!='#skF_8' | ~r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_82])).
% 5.13/2.05  tff(c_138, plain, (~r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 5.13/2.05  tff(c_88, plain, (r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_8') | k2_subset_1('#skF_7')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.13/2.05  tff(c_91, plain, (r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_8') | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_88])).
% 5.13/2.05  tff(c_161, plain, ('#skF_7'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_138, c_91])).
% 5.13/2.05  tff(c_80, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.13/2.05  tff(c_163, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_80])).
% 5.13/2.05  tff(c_673, plain, (![A_111, B_112]: (k4_xboole_0(A_111, B_112)=k3_subset_1(A_111, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.13/2.05  tff(c_686, plain, (k4_xboole_0('#skF_8', '#skF_8')=k3_subset_1('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_163, c_673])).
% 5.13/2.05  tff(c_696, plain, (k3_subset_1('#skF_8', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_320, c_686])).
% 5.13/2.05  tff(c_162, plain, (~r1_tarski(k3_subset_1('#skF_8', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_138])).
% 5.13/2.05  tff(c_698, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_162])).
% 5.13/2.05  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_698])).
% 5.13/2.05  tff(c_702, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_90])).
% 5.13/2.05  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.13/2.05  tff(c_2192, plain, (![A_202, B_203]: (k4_xboole_0(A_202, B_203)=k3_subset_1(A_202, B_203) | ~m1_subset_1(B_203, k1_zfmisc_1(A_202)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.13/2.05  tff(c_2210, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_2192])).
% 5.13/2.05  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.13/2.05  tff(c_2399, plain, (![D_208]: (r2_hidden(D_208, '#skF_7') | ~r2_hidden(D_208, k3_subset_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2210, c_12])).
% 5.13/2.05  tff(c_2414, plain, (r2_hidden('#skF_4'(k3_subset_1('#skF_7', '#skF_8')), '#skF_7') | k3_subset_1('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_2399])).
% 5.13/2.05  tff(c_4544, plain, (k3_subset_1('#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2414])).
% 5.13/2.05  tff(c_1960, plain, (![A_197, B_198]: (k3_subset_1(A_197, k3_subset_1(A_197, B_198))=B_198 | ~m1_subset_1(B_198, k1_zfmisc_1(A_197)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.13/2.05  tff(c_1974, plain, (k3_subset_1('#skF_7', k3_subset_1('#skF_7', '#skF_8'))='#skF_8'), inference(resolution, [status(thm)], [c_80, c_1960])).
% 5.13/2.05  tff(c_4557, plain, (k3_subset_1('#skF_7', k1_xboole_0)='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_1974])).
% 5.13/2.05  tff(c_68, plain, (![A_36]: (k1_subset_1(A_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.13/2.05  tff(c_78, plain, (![A_43]: (k3_subset_1(A_43, k1_subset_1(A_43))=k2_subset_1(A_43))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.13/2.05  tff(c_89, plain, (![A_43]: (k3_subset_1(A_43, k1_subset_1(A_43))=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_78])).
% 5.13/2.05  tff(c_92, plain, (![A_43]: (k3_subset_1(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_89])).
% 5.13/2.05  tff(c_4619, plain, ('#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_4557, c_92])).
% 5.13/2.05  tff(c_4626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_702, c_4619])).
% 5.13/2.05  tff(c_4628, plain, (k3_subset_1('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2414])).
% 5.13/2.05  tff(c_703, plain, (r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 5.13/2.05  tff(c_1593, plain, (![C_183, B_184, A_185]: (r2_hidden(C_183, B_184) | ~r2_hidden(C_183, A_185) | ~r1_tarski(A_185, B_184))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.13/2.05  tff(c_4629, plain, (![A_278, B_279]: (r2_hidden('#skF_4'(A_278), B_279) | ~r1_tarski(A_278, B_279) | k1_xboole_0=A_278)), inference(resolution, [status(thm)], [c_28, c_1593])).
% 5.13/2.05  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.13/2.05  tff(c_2770, plain, (![D_217]: (~r2_hidden(D_217, '#skF_8') | ~r2_hidden(D_217, k3_subset_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2210, c_10])).
% 5.13/2.05  tff(c_2785, plain, (~r2_hidden('#skF_4'(k3_subset_1('#skF_7', '#skF_8')), '#skF_8') | k3_subset_1('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_2770])).
% 5.13/2.05  tff(c_4389, plain, (~r2_hidden('#skF_4'(k3_subset_1('#skF_7', '#skF_8')), '#skF_8')), inference(splitLeft, [status(thm)], [c_2785])).
% 5.13/2.05  tff(c_4640, plain, (~r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_8') | k3_subset_1('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_4629, c_4389])).
% 5.13/2.05  tff(c_4688, plain, (k3_subset_1('#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_703, c_4640])).
% 5.13/2.05  tff(c_4702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4628, c_4688])).
% 5.13/2.05  tff(c_4703, plain, (k3_subset_1('#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2785])).
% 5.13/2.05  tff(c_4715, plain, (k3_subset_1('#skF_7', k1_xboole_0)='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4703, c_1974])).
% 5.13/2.05  tff(c_4757, plain, ('#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_4715, c_92])).
% 5.13/2.05  tff(c_4764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_702, c_4757])).
% 5.13/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/2.05  
% 5.13/2.05  Inference rules
% 5.13/2.05  ----------------------
% 5.13/2.05  #Ref     : 0
% 5.13/2.05  #Sup     : 1122
% 5.13/2.05  #Fact    : 0
% 5.13/2.05  #Define  : 0
% 5.13/2.05  #Split   : 9
% 5.13/2.05  #Chain   : 0
% 5.13/2.05  #Close   : 0
% 5.13/2.05  
% 5.13/2.05  Ordering : KBO
% 5.13/2.05  
% 5.13/2.05  Simplification rules
% 5.13/2.05  ----------------------
% 5.13/2.05  #Subsume      : 96
% 5.13/2.05  #Demod        : 543
% 5.13/2.05  #Tautology    : 575
% 5.13/2.05  #SimpNegUnit  : 33
% 5.13/2.05  #BackRed      : 37
% 5.13/2.05  
% 5.13/2.05  #Partial instantiations: 0
% 5.13/2.05  #Strategies tried      : 1
% 5.13/2.05  
% 5.13/2.05  Timing (in seconds)
% 5.13/2.05  ----------------------
% 5.13/2.05  Preprocessing        : 0.36
% 5.13/2.05  Parsing              : 0.18
% 5.13/2.05  CNF conversion       : 0.03
% 5.13/2.05  Main loop            : 0.88
% 5.13/2.05  Inferencing          : 0.29
% 5.13/2.05  Reduction            : 0.31
% 5.13/2.05  Demodulation         : 0.23
% 5.13/2.05  BG Simplification    : 0.04
% 5.13/2.05  Subsumption          : 0.15
% 5.13/2.05  Abstraction          : 0.04
% 5.13/2.05  MUC search           : 0.00
% 5.13/2.05  Cooper               : 0.00
% 5.13/2.05  Total                : 1.28
% 5.13/2.05  Index Insertion      : 0.00
% 5.13/2.05  Index Deletion       : 0.00
% 5.13/2.06  Index Matching       : 0.00
% 5.13/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
