%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:18 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 114 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 186 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_100,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_71,axiom,(
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

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_61,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,(
    ! [A_62,C_63,B_64] :
      ( ~ r2_hidden(A_62,C_63)
      | ~ r1_xboole_0(k2_tarski(A_62,B_64),C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    ! [A_65] : ~ r2_hidden(A_65,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_90])).

tff(c_26,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k5_relat_1(A_39,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_143,plain,(
    ! [A_85,B_86] :
      ( k1_relat_1(k5_relat_1(A_85,B_86)) = k1_relat_1(A_85)
      | ~ r1_tarski(k2_relat_1(A_85),k1_relat_1(B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_149,plain,(
    ! [B_86] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_86)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_143])).

tff(c_165,plain,(
    ! [B_89] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_89)) = k1_xboole_0
      | ~ v1_relat_1(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_6,c_38,c_149])).

tff(c_28,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k1_relat_1(A_41))
      | ~ v1_relat_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_177,plain,(
    ! [B_89] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_89))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_28])).

tff(c_209,plain,(
    ! [B_91] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_91))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_91))
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_214,plain,(
    ! [B_92] :
      ( k5_relat_1(k1_xboole_0,B_92) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_209,c_4])).

tff(c_218,plain,(
    ! [B_40] :
      ( k5_relat_1(k1_xboole_0,B_40) = k1_xboole_0
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_214])).

tff(c_222,plain,(
    ! [B_93] :
      ( k5_relat_1(k1_xboole_0,B_93) = k1_xboole_0
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_218])).

tff(c_231,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_222])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_231])).

tff(c_238,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_265,plain,(
    ! [A_98,C_99,B_100] :
      ( ~ r2_hidden(A_98,C_99)
      | ~ r1_xboole_0(k2_tarski(A_98,B_100),C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_271,plain,(
    ! [A_101] : ~ r2_hidden(A_101,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_265])).

tff(c_276,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_271])).

tff(c_373,plain,(
    ! [B_127,A_128] :
      ( k2_relat_1(k5_relat_1(B_127,A_128)) = k2_relat_1(A_128)
      | ~ r1_tarski(k1_relat_1(A_128),k2_relat_1(B_127))
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_379,plain,(
    ! [B_127] :
      ( k2_relat_1(k5_relat_1(B_127,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_127))
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_373])).

tff(c_389,plain,(
    ! [B_129] :
      ( k2_relat_1(k5_relat_1(B_129,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_6,c_36,c_379])).

tff(c_30,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k2_relat_1(A_42))
      | ~ v1_relat_1(A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_401,plain,(
    ! [B_129] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_129,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_129,k1_xboole_0))
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_30])).

tff(c_411,plain,(
    ! [B_130] :
      ( ~ v1_relat_1(k5_relat_1(B_130,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_130,k1_xboole_0))
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_401])).

tff(c_483,plain,(
    ! [B_134] :
      ( k5_relat_1(B_134,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_134,k1_xboole_0))
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_411,c_4])).

tff(c_490,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_26,c_483])).

tff(c_496,plain,(
    ! [A_135] :
      ( k5_relat_1(A_135,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_490])).

tff(c_505,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_496])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:22:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.34  
% 2.18/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.58/1.34  
% 2.58/1.34  %Foreground sorts:
% 2.58/1.34  
% 2.58/1.34  
% 2.58/1.34  %Background operators:
% 2.58/1.34  
% 2.58/1.34  
% 2.58/1.34  %Foreground operators:
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.58/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.58/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.58/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.34  
% 2.58/1.36  tff(f_107, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.58/1.36  tff(f_57, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.58/1.36  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.58/1.36  tff(f_47, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.58/1.36  tff(f_63, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.58/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.36  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.58/1.36  tff(f_100, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.58/1.36  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.58/1.36  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.58/1.36  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.58/1.36  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.58/1.36  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.58/1.36  tff(c_40, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.58/1.36  tff(c_61, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.58/1.36  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.58/1.36  tff(c_24, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.58/1.36  tff(c_8, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.58/1.36  tff(c_84, plain, (![A_62, C_63, B_64]: (~r2_hidden(A_62, C_63) | ~r1_xboole_0(k2_tarski(A_62, B_64), C_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.36  tff(c_90, plain, (![A_65]: (~r2_hidden(A_65, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_84])).
% 2.58/1.36  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_90])).
% 2.58/1.36  tff(c_26, plain, (![A_39, B_40]: (v1_relat_1(k5_relat_1(A_39, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.36  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.36  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.36  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.36  tff(c_143, plain, (![A_85, B_86]: (k1_relat_1(k5_relat_1(A_85, B_86))=k1_relat_1(A_85) | ~r1_tarski(k2_relat_1(A_85), k1_relat_1(B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.58/1.36  tff(c_149, plain, (![B_86]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_86))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_143])).
% 2.58/1.36  tff(c_165, plain, (![B_89]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_89))=k1_xboole_0 | ~v1_relat_1(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_6, c_38, c_149])).
% 2.58/1.36  tff(c_28, plain, (![A_41]: (~v1_xboole_0(k1_relat_1(A_41)) | ~v1_relat_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.36  tff(c_177, plain, (![B_89]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_89)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_89)) | ~v1_relat_1(B_89))), inference(superposition, [status(thm), theory('equality')], [c_165, c_28])).
% 2.58/1.36  tff(c_209, plain, (![B_91]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_91)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_91)) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_177])).
% 2.58/1.36  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.58/1.36  tff(c_214, plain, (![B_92]: (k5_relat_1(k1_xboole_0, B_92)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_92)) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_209, c_4])).
% 2.58/1.36  tff(c_218, plain, (![B_40]: (k5_relat_1(k1_xboole_0, B_40)=k1_xboole_0 | ~v1_relat_1(B_40) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_214])).
% 2.58/1.36  tff(c_222, plain, (![B_93]: (k5_relat_1(k1_xboole_0, B_93)=k1_xboole_0 | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_218])).
% 2.58/1.36  tff(c_231, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_222])).
% 2.58/1.36  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_231])).
% 2.58/1.36  tff(c_238, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.58/1.36  tff(c_265, plain, (![A_98, C_99, B_100]: (~r2_hidden(A_98, C_99) | ~r1_xboole_0(k2_tarski(A_98, B_100), C_99))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.36  tff(c_271, plain, (![A_101]: (~r2_hidden(A_101, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_265])).
% 2.58/1.36  tff(c_276, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_271])).
% 2.58/1.36  tff(c_373, plain, (![B_127, A_128]: (k2_relat_1(k5_relat_1(B_127, A_128))=k2_relat_1(A_128) | ~r1_tarski(k1_relat_1(A_128), k2_relat_1(B_127)) | ~v1_relat_1(B_127) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.58/1.36  tff(c_379, plain, (![B_127]: (k2_relat_1(k5_relat_1(B_127, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_127)) | ~v1_relat_1(B_127) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_373])).
% 2.58/1.36  tff(c_389, plain, (![B_129]: (k2_relat_1(k5_relat_1(B_129, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_6, c_36, c_379])).
% 2.58/1.36  tff(c_30, plain, (![A_42]: (~v1_xboole_0(k2_relat_1(A_42)) | ~v1_relat_1(A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.58/1.36  tff(c_401, plain, (![B_129]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_129, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_129, k1_xboole_0)) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_389, c_30])).
% 2.58/1.36  tff(c_411, plain, (![B_130]: (~v1_relat_1(k5_relat_1(B_130, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_130, k1_xboole_0)) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_401])).
% 2.58/1.36  tff(c_483, plain, (![B_134]: (k5_relat_1(B_134, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_134, k1_xboole_0)) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_411, c_4])).
% 2.58/1.36  tff(c_490, plain, (![A_39]: (k5_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_26, c_483])).
% 2.58/1.36  tff(c_496, plain, (![A_135]: (k5_relat_1(A_135, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_490])).
% 2.58/1.36  tff(c_505, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_496])).
% 2.58/1.36  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_505])).
% 2.58/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.36  
% 2.58/1.36  Inference rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Ref     : 2
% 2.58/1.36  #Sup     : 96
% 2.58/1.36  #Fact    : 0
% 2.58/1.36  #Define  : 0
% 2.58/1.36  #Split   : 1
% 2.58/1.36  #Chain   : 0
% 2.58/1.36  #Close   : 0
% 2.58/1.36  
% 2.58/1.36  Ordering : KBO
% 2.58/1.36  
% 2.58/1.36  Simplification rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Subsume      : 3
% 2.58/1.36  #Demod        : 73
% 2.58/1.36  #Tautology    : 56
% 2.58/1.36  #SimpNegUnit  : 2
% 2.58/1.36  #BackRed      : 0
% 2.58/1.36  
% 2.58/1.36  #Partial instantiations: 0
% 2.58/1.36  #Strategies tried      : 1
% 2.58/1.36  
% 2.58/1.36  Timing (in seconds)
% 2.58/1.36  ----------------------
% 2.58/1.36  Preprocessing        : 0.33
% 2.58/1.36  Parsing              : 0.18
% 2.58/1.36  CNF conversion       : 0.02
% 2.58/1.36  Main loop            : 0.25
% 2.58/1.36  Inferencing          : 0.11
% 2.58/1.36  Reduction            : 0.07
% 2.58/1.36  Demodulation         : 0.05
% 2.58/1.36  BG Simplification    : 0.02
% 2.58/1.36  Subsumption          : 0.04
% 2.58/1.36  Abstraction          : 0.02
% 2.58/1.36  MUC search           : 0.00
% 2.58/1.36  Cooper               : 0.00
% 2.58/1.36  Total                : 0.62
% 2.58/1.36  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
