%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:23 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 159 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 322 expanded)
%              Number of equality atoms :   67 ( 278 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_40,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_63,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_435,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(B_81) = A_82
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_tarski(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_449,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_76,c_435])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_63,c_449])).

tff(c_461,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_462,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_464,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_2') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_12])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_463,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_462,c_8])).

tff(c_636,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_645,plain,(
    ! [A_8] : k5_xboole_0(A_8,'#skF_2') = k4_xboole_0(A_8,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_636])).

tff(c_649,plain,(
    ! [A_107] : k4_xboole_0(A_107,'#skF_2') = A_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_645])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_490,plain,(
    ! [A_89,B_90] :
      ( k2_xboole_0(A_89,B_90) = B_90
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_503,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_490])).

tff(c_655,plain,(
    ! [A_107] : k2_xboole_0(A_107,A_107) = A_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_503])).

tff(c_658,plain,(
    ! [A_107] : r1_tarski(A_107,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_10])).

tff(c_616,plain,(
    ! [A_102,C_103,B_104] :
      ( r1_tarski(A_102,k2_xboole_0(C_103,B_104))
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_634,plain,(
    ! [A_102] :
      ( r1_tarski(A_102,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_102,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_616])).

tff(c_30,plain,(
    ! [B_43,A_42] :
      ( k1_tarski(B_43) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_tarski(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_758,plain,(
    ! [B_117,A_118] :
      ( k1_tarski(B_117) = A_118
      | A_118 = '#skF_2'
      | ~ r1_tarski(A_118,k1_tarski(B_117)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_30])).

tff(c_779,plain,(
    ! [A_119] :
      ( k1_tarski('#skF_1') = A_119
      | A_119 = '#skF_2'
      | ~ r1_tarski(A_119,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_634,c_758])).

tff(c_783,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_658,c_779])).

tff(c_790,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_783])).

tff(c_800,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_44])).

tff(c_802,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_800])).

tff(c_804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_802])).

tff(c_805,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_806,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_841,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_806,c_42])).

tff(c_1026,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k3_xboole_0(A_136,B_137)) = k4_xboole_0(A_136,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1035,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1026])).

tff(c_1039,plain,(
    ! [A_138] : k4_xboole_0(A_138,k1_xboole_0) = A_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1035])).

tff(c_1048,plain,(
    ! [A_138] : r1_tarski(A_138,A_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_10])).

tff(c_814,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_44])).

tff(c_1104,plain,(
    ! [A_142,C_143,B_144] :
      ( r1_tarski(A_142,k2_xboole_0(C_143,B_144))
      | ~ r1_tarski(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1133,plain,(
    ! [A_148] :
      ( r1_tarski(A_148,'#skF_2')
      | ~ r1_tarski(A_148,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1104])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1138,plain,(
    ! [A_149] :
      ( k2_xboole_0(A_149,'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_149,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1133,c_6])).

tff(c_1147,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1048,c_1138])).

tff(c_1155,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_14])).

tff(c_1246,plain,(
    ! [B_154,A_155] :
      ( k1_tarski(B_154) = A_155
      | k1_xboole_0 = A_155
      | ~ r1_tarski(A_155,k1_tarski(B_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1257,plain,(
    ! [A_155] :
      ( k1_tarski('#skF_1') = A_155
      | k1_xboole_0 = A_155
      | ~ r1_tarski(A_155,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_1246])).

tff(c_1276,plain,(
    ! [A_160] :
      ( A_160 = '#skF_2'
      | k1_xboole_0 = A_160
      | ~ r1_tarski(A_160,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_1257])).

tff(c_1282,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1155,c_1276])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_805,c_841,c_1282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:04:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.43  
% 2.88/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.43  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.43  
% 2.88/1.43  %Foreground sorts:
% 2.88/1.43  
% 2.88/1.43  
% 2.88/1.43  %Background operators:
% 2.88/1.43  
% 2.88/1.43  
% 2.88/1.43  %Foreground operators:
% 2.88/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.88/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.88/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.88/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.43  
% 2.98/1.44  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.98/1.44  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.98/1.44  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.98/1.44  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.98/1.44  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.98/1.44  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.98/1.44  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.98/1.44  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.98/1.44  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.98/1.44  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.44  tff(c_80, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 2.98/1.44  tff(c_38, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.44  tff(c_63, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 2.98/1.44  tff(c_44, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.44  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.98/1.44  tff(c_76, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_14])).
% 2.98/1.44  tff(c_435, plain, (![B_81, A_82]: (k1_tarski(B_81)=A_82 | k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_tarski(B_81)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.98/1.44  tff(c_449, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_76, c_435])).
% 2.98/1.44  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_63, c_449])).
% 2.98/1.44  tff(c_461, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 2.98/1.44  tff(c_462, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 2.98/1.44  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.44  tff(c_464, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_2')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_462, c_12])).
% 2.98/1.44  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.44  tff(c_463, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_462, c_8])).
% 2.98/1.44  tff(c_636, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.98/1.44  tff(c_645, plain, (![A_8]: (k5_xboole_0(A_8, '#skF_2')=k4_xboole_0(A_8, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_463, c_636])).
% 2.98/1.44  tff(c_649, plain, (![A_107]: (k4_xboole_0(A_107, '#skF_2')=A_107)), inference(demodulation, [status(thm), theory('equality')], [c_464, c_645])).
% 2.98/1.44  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.44  tff(c_490, plain, (![A_89, B_90]: (k2_xboole_0(A_89, B_90)=B_90 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.44  tff(c_503, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_10, c_490])).
% 2.98/1.44  tff(c_655, plain, (![A_107]: (k2_xboole_0(A_107, A_107)=A_107)), inference(superposition, [status(thm), theory('equality')], [c_649, c_503])).
% 2.98/1.44  tff(c_658, plain, (![A_107]: (r1_tarski(A_107, A_107))), inference(superposition, [status(thm), theory('equality')], [c_649, c_10])).
% 2.98/1.44  tff(c_616, plain, (![A_102, C_103, B_104]: (r1_tarski(A_102, k2_xboole_0(C_103, B_104)) | ~r1_tarski(A_102, B_104))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.44  tff(c_634, plain, (![A_102]: (r1_tarski(A_102, k1_tarski('#skF_1')) | ~r1_tarski(A_102, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_616])).
% 2.98/1.44  tff(c_30, plain, (![B_43, A_42]: (k1_tarski(B_43)=A_42 | k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_tarski(B_43)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.98/1.44  tff(c_758, plain, (![B_117, A_118]: (k1_tarski(B_117)=A_118 | A_118='#skF_2' | ~r1_tarski(A_118, k1_tarski(B_117)))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_30])).
% 2.98/1.44  tff(c_779, plain, (![A_119]: (k1_tarski('#skF_1')=A_119 | A_119='#skF_2' | ~r1_tarski(A_119, '#skF_3'))), inference(resolution, [status(thm)], [c_634, c_758])).
% 2.98/1.44  tff(c_783, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_658, c_779])).
% 2.98/1.44  tff(c_790, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_461, c_783])).
% 2.98/1.44  tff(c_800, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_44])).
% 2.98/1.44  tff(c_802, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_655, c_800])).
% 2.98/1.44  tff(c_804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_802])).
% 2.98/1.44  tff(c_805, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.98/1.44  tff(c_806, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 2.98/1.44  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.44  tff(c_841, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_806, c_806, c_42])).
% 2.98/1.44  tff(c_1026, plain, (![A_136, B_137]: (k5_xboole_0(A_136, k3_xboole_0(A_136, B_137))=k4_xboole_0(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.98/1.44  tff(c_1035, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1026])).
% 2.98/1.44  tff(c_1039, plain, (![A_138]: (k4_xboole_0(A_138, k1_xboole_0)=A_138)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1035])).
% 2.98/1.44  tff(c_1048, plain, (![A_138]: (r1_tarski(A_138, A_138))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_10])).
% 2.98/1.44  tff(c_814, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_806, c_44])).
% 2.98/1.44  tff(c_1104, plain, (![A_142, C_143, B_144]: (r1_tarski(A_142, k2_xboole_0(C_143, B_144)) | ~r1_tarski(A_142, B_144))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.44  tff(c_1133, plain, (![A_148]: (r1_tarski(A_148, '#skF_2') | ~r1_tarski(A_148, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_814, c_1104])).
% 2.98/1.44  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.44  tff(c_1138, plain, (![A_149]: (k2_xboole_0(A_149, '#skF_2')='#skF_2' | ~r1_tarski(A_149, '#skF_3'))), inference(resolution, [status(thm)], [c_1133, c_6])).
% 2.98/1.44  tff(c_1147, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_1048, c_1138])).
% 2.98/1.44  tff(c_1155, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1147, c_14])).
% 2.98/1.44  tff(c_1246, plain, (![B_154, A_155]: (k1_tarski(B_154)=A_155 | k1_xboole_0=A_155 | ~r1_tarski(A_155, k1_tarski(B_154)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.98/1.44  tff(c_1257, plain, (![A_155]: (k1_tarski('#skF_1')=A_155 | k1_xboole_0=A_155 | ~r1_tarski(A_155, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_806, c_1246])).
% 2.98/1.44  tff(c_1276, plain, (![A_160]: (A_160='#skF_2' | k1_xboole_0=A_160 | ~r1_tarski(A_160, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_1257])).
% 2.98/1.44  tff(c_1282, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1155, c_1276])).
% 2.98/1.44  tff(c_1301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_805, c_841, c_1282])).
% 2.98/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.44  
% 2.98/1.44  Inference rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Ref     : 0
% 2.98/1.44  #Sup     : 297
% 2.98/1.44  #Fact    : 0
% 2.98/1.44  #Define  : 0
% 2.98/1.44  #Split   : 3
% 2.98/1.44  #Chain   : 0
% 2.98/1.44  #Close   : 0
% 2.98/1.44  
% 2.98/1.44  Ordering : KBO
% 2.98/1.44  
% 2.98/1.44  Simplification rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Subsume      : 3
% 2.98/1.44  #Demod        : 155
% 2.98/1.44  #Tautology    : 243
% 2.98/1.44  #SimpNegUnit  : 4
% 2.98/1.44  #BackRed      : 23
% 2.98/1.44  
% 2.98/1.44  #Partial instantiations: 0
% 2.98/1.44  #Strategies tried      : 1
% 2.98/1.44  
% 2.98/1.44  Timing (in seconds)
% 2.98/1.44  ----------------------
% 2.98/1.45  Preprocessing        : 0.32
% 2.98/1.45  Parsing              : 0.18
% 2.98/1.45  CNF conversion       : 0.02
% 2.98/1.45  Main loop            : 0.36
% 2.98/1.45  Inferencing          : 0.14
% 2.98/1.45  Reduction            : 0.12
% 2.98/1.45  Demodulation         : 0.09
% 2.98/1.45  BG Simplification    : 0.02
% 2.98/1.45  Subsumption          : 0.05
% 2.98/1.45  Abstraction          : 0.02
% 2.98/1.45  MUC search           : 0.00
% 2.98/1.45  Cooper               : 0.00
% 2.98/1.45  Total                : 0.71
% 2.98/1.45  Index Insertion      : 0.00
% 2.98/1.45  Index Deletion       : 0.00
% 2.98/1.45  Index Matching       : 0.00
% 2.98/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
