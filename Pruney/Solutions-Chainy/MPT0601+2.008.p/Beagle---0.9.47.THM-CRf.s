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
% DateTime   : Thu Dec  3 10:02:15 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   74 (  93 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 170 expanded)
%              Number of equality atoms :   48 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_60,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_139,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_66])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(k1_tarski(A_12),B_13)
      | r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_186,plain,(
    ! [A_64,B_65] :
      ( k7_relat_1(A_64,B_65) = k1_xboole_0
      | ~ r1_xboole_0(B_65,k1_relat_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_308,plain,(
    ! [A_83,A_84] :
      ( k7_relat_1(A_83,k1_tarski(A_84)) = k1_xboole_0
      | ~ v1_relat_1(A_83)
      | r2_hidden(A_84,k1_relat_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_315,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_308,c_106])).

tff(c_322,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_315])).

tff(c_197,plain,(
    ! [B_66,A_67] :
      ( r1_xboole_0(k1_relat_1(B_66),A_67)
      | k7_relat_1(B_66,A_67) != k1_xboole_0
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( k9_relat_1(B_21,A_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_231,plain,(
    ! [B_70,A_71] :
      ( k9_relat_1(B_70,A_71) = k1_xboole_0
      | k7_relat_1(B_70,A_71) != k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_197,c_38])).

tff(c_235,plain,(
    ! [A_72] :
      ( k9_relat_1('#skF_4',A_72) = k1_xboole_0
      | k7_relat_1('#skF_4',A_72) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_231])).

tff(c_36,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    ! [B_19] :
      ( k11_relat_1('#skF_4',B_19) = k1_xboole_0
      | ~ v1_relat_1('#skF_4')
      | k7_relat_1('#skF_4',k1_tarski(B_19)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_36])).

tff(c_261,plain,(
    ! [B_19] :
      ( k11_relat_1('#skF_4',B_19) = k1_xboole_0
      | k7_relat_1('#skF_4',k1_tarski(B_19)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_245])).

tff(c_327,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_261])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_327])).

tff(c_337,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [E_8,B_3,C_4] : r2_hidden(E_8,k1_enumset1(E_8,B_3,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_343,plain,(
    ! [A_85,B_86] : r2_hidden(A_85,k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_346,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_343])).

tff(c_338,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_357,plain,(
    ! [A_92,C_93,B_94] :
      ( ~ r2_hidden(A_92,C_93)
      | ~ r1_xboole_0(k2_tarski(A_92,B_94),C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_365,plain,(
    ! [A_92] : ~ r2_hidden(A_92,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_357])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_447,plain,(
    ! [B_110,A_111] :
      ( r1_xboole_0(k1_relat_1(B_110),A_111)
      | k9_relat_1(B_110,A_111) != k1_xboole_0
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_506,plain,(
    ! [B_116,A_117] :
      ( k7_relat_1(B_116,A_117) = k1_xboole_0
      | k9_relat_1(B_116,A_117) != k1_xboole_0
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_447,c_54])).

tff(c_512,plain,(
    ! [A_17,B_19] :
      ( k7_relat_1(A_17,k1_tarski(B_19)) = k1_xboole_0
      | k11_relat_1(A_17,B_19) != k1_xboole_0
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_506])).

tff(c_610,plain,(
    ! [A_137,C_138,B_139] :
      ( r2_hidden(A_137,k1_relat_1(k7_relat_1(C_138,B_139)))
      | ~ r2_hidden(A_137,k1_relat_1(C_138))
      | ~ r2_hidden(A_137,B_139)
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_619,plain,(
    ! [A_137,A_17,B_19] :
      ( r2_hidden(A_137,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_137,k1_relat_1(A_17))
      | ~ r2_hidden(A_137,k1_tarski(B_19))
      | ~ v1_relat_1(A_17)
      | k11_relat_1(A_17,B_19) != k1_xboole_0
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_610])).

tff(c_625,plain,(
    ! [A_137,A_17,B_19] :
      ( r2_hidden(A_137,k1_xboole_0)
      | ~ r2_hidden(A_137,k1_relat_1(A_17))
      | ~ r2_hidden(A_137,k1_tarski(B_19))
      | ~ v1_relat_1(A_17)
      | k11_relat_1(A_17,B_19) != k1_xboole_0
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_619])).

tff(c_787,plain,(
    ! [A_163,A_164,B_165] :
      ( ~ r2_hidden(A_163,k1_relat_1(A_164))
      | ~ r2_hidden(A_163,k1_tarski(B_165))
      | ~ v1_relat_1(A_164)
      | k11_relat_1(A_164,B_165) != k1_xboole_0
      | ~ v1_relat_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_625])).

tff(c_793,plain,(
    ! [B_165] :
      ( ~ r2_hidden('#skF_3',k1_tarski(B_165))
      | k11_relat_1('#skF_4',B_165) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_338,c_787])).

tff(c_801,plain,(
    ! [B_166] :
      ( ~ r2_hidden('#skF_3',k1_tarski(B_166))
      | k11_relat_1('#skF_4',B_166) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_793])).

tff(c_805,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_346,c_801])).

tff(c_809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:51:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.45  
% 2.91/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.45  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.91/1.45  
% 2.91/1.45  %Foreground sorts:
% 2.91/1.45  
% 2.91/1.45  
% 2.91/1.45  %Background operators:
% 2.91/1.45  
% 2.91/1.45  
% 2.91/1.45  %Foreground operators:
% 2.91/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.91/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.45  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.91/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.91/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.91/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.91/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.45  
% 3.07/1.46  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.07/1.46  tff(f_51, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.07/1.46  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 3.07/1.46  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.07/1.46  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.07/1.46  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.07/1.46  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.07/1.46  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.07/1.46  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.07/1.46  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.07/1.46  tff(f_56, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.07/1.46  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.07/1.46  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.07/1.46  tff(c_60, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.46  tff(c_106, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.07/1.46  tff(c_66, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.46  tff(c_139, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_106, c_66])).
% 3.07/1.46  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.46  tff(c_32, plain, (![A_12, B_13]: (r1_xboole_0(k1_tarski(A_12), B_13) | r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.46  tff(c_186, plain, (![A_64, B_65]: (k7_relat_1(A_64, B_65)=k1_xboole_0 | ~r1_xboole_0(B_65, k1_relat_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.07/1.46  tff(c_308, plain, (![A_83, A_84]: (k7_relat_1(A_83, k1_tarski(A_84))=k1_xboole_0 | ~v1_relat_1(A_83) | r2_hidden(A_84, k1_relat_1(A_83)))), inference(resolution, [status(thm)], [c_32, c_186])).
% 3.07/1.46  tff(c_315, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_308, c_106])).
% 3.07/1.46  tff(c_322, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_315])).
% 3.07/1.46  tff(c_197, plain, (![B_66, A_67]: (r1_xboole_0(k1_relat_1(B_66), A_67) | k7_relat_1(B_66, A_67)!=k1_xboole_0 | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.07/1.46  tff(c_38, plain, (![B_21, A_20]: (k9_relat_1(B_21, A_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.07/1.46  tff(c_231, plain, (![B_70, A_71]: (k9_relat_1(B_70, A_71)=k1_xboole_0 | k7_relat_1(B_70, A_71)!=k1_xboole_0 | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_197, c_38])).
% 3.07/1.46  tff(c_235, plain, (![A_72]: (k9_relat_1('#skF_4', A_72)=k1_xboole_0 | k7_relat_1('#skF_4', A_72)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_231])).
% 3.07/1.46  tff(c_36, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.07/1.46  tff(c_245, plain, (![B_19]: (k11_relat_1('#skF_4', B_19)=k1_xboole_0 | ~v1_relat_1('#skF_4') | k7_relat_1('#skF_4', k1_tarski(B_19))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_235, c_36])).
% 3.07/1.46  tff(c_261, plain, (![B_19]: (k11_relat_1('#skF_4', B_19)=k1_xboole_0 | k7_relat_1('#skF_4', k1_tarski(B_19))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_245])).
% 3.07/1.46  tff(c_327, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_322, c_261])).
% 3.07/1.46  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_327])).
% 3.07/1.46  tff(c_337, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.07/1.46  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.07/1.46  tff(c_88, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.46  tff(c_10, plain, (![E_8, B_3, C_4]: (r2_hidden(E_8, k1_enumset1(E_8, B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.46  tff(c_343, plain, (![A_85, B_86]: (r2_hidden(A_85, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_10])).
% 3.07/1.46  tff(c_346, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_343])).
% 3.07/1.46  tff(c_338, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 3.07/1.46  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.46  tff(c_357, plain, (![A_92, C_93, B_94]: (~r2_hidden(A_92, C_93) | ~r1_xboole_0(k2_tarski(A_92, B_94), C_93))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.07/1.46  tff(c_365, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_357])).
% 3.07/1.46  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.07/1.46  tff(c_447, plain, (![B_110, A_111]: (r1_xboole_0(k1_relat_1(B_110), A_111) | k9_relat_1(B_110, A_111)!=k1_xboole_0 | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.07/1.46  tff(c_54, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.07/1.46  tff(c_506, plain, (![B_116, A_117]: (k7_relat_1(B_116, A_117)=k1_xboole_0 | k9_relat_1(B_116, A_117)!=k1_xboole_0 | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_447, c_54])).
% 3.07/1.46  tff(c_512, plain, (![A_17, B_19]: (k7_relat_1(A_17, k1_tarski(B_19))=k1_xboole_0 | k11_relat_1(A_17, B_19)!=k1_xboole_0 | ~v1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_36, c_506])).
% 3.07/1.46  tff(c_610, plain, (![A_137, C_138, B_139]: (r2_hidden(A_137, k1_relat_1(k7_relat_1(C_138, B_139))) | ~r2_hidden(A_137, k1_relat_1(C_138)) | ~r2_hidden(A_137, B_139) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.07/1.46  tff(c_619, plain, (![A_137, A_17, B_19]: (r2_hidden(A_137, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_137, k1_relat_1(A_17)) | ~r2_hidden(A_137, k1_tarski(B_19)) | ~v1_relat_1(A_17) | k11_relat_1(A_17, B_19)!=k1_xboole_0 | ~v1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_512, c_610])).
% 3.07/1.46  tff(c_625, plain, (![A_137, A_17, B_19]: (r2_hidden(A_137, k1_xboole_0) | ~r2_hidden(A_137, k1_relat_1(A_17)) | ~r2_hidden(A_137, k1_tarski(B_19)) | ~v1_relat_1(A_17) | k11_relat_1(A_17, B_19)!=k1_xboole_0 | ~v1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_619])).
% 3.07/1.46  tff(c_787, plain, (![A_163, A_164, B_165]: (~r2_hidden(A_163, k1_relat_1(A_164)) | ~r2_hidden(A_163, k1_tarski(B_165)) | ~v1_relat_1(A_164) | k11_relat_1(A_164, B_165)!=k1_xboole_0 | ~v1_relat_1(A_164) | ~v1_relat_1(A_164))), inference(negUnitSimplification, [status(thm)], [c_365, c_625])).
% 3.07/1.46  tff(c_793, plain, (![B_165]: (~r2_hidden('#skF_3', k1_tarski(B_165)) | k11_relat_1('#skF_4', B_165)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_338, c_787])).
% 3.07/1.46  tff(c_801, plain, (![B_166]: (~r2_hidden('#skF_3', k1_tarski(B_166)) | k11_relat_1('#skF_4', B_166)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_793])).
% 3.07/1.46  tff(c_805, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_346, c_801])).
% 3.07/1.46  tff(c_809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_337, c_805])).
% 3.07/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.46  
% 3.07/1.46  Inference rules
% 3.07/1.46  ----------------------
% 3.07/1.46  #Ref     : 0
% 3.07/1.46  #Sup     : 164
% 3.07/1.46  #Fact    : 0
% 3.07/1.46  #Define  : 0
% 3.07/1.46  #Split   : 3
% 3.07/1.46  #Chain   : 0
% 3.07/1.46  #Close   : 0
% 3.07/1.46  
% 3.07/1.46  Ordering : KBO
% 3.07/1.46  
% 3.07/1.46  Simplification rules
% 3.07/1.46  ----------------------
% 3.07/1.46  #Subsume      : 30
% 3.07/1.46  #Demod        : 49
% 3.07/1.46  #Tautology    : 72
% 3.07/1.46  #SimpNegUnit  : 11
% 3.07/1.46  #BackRed      : 0
% 3.07/1.46  
% 3.07/1.46  #Partial instantiations: 0
% 3.07/1.46  #Strategies tried      : 1
% 3.07/1.46  
% 3.07/1.46  Timing (in seconds)
% 3.07/1.46  ----------------------
% 3.07/1.47  Preprocessing        : 0.32
% 3.07/1.47  Parsing              : 0.16
% 3.07/1.47  CNF conversion       : 0.02
% 3.07/1.47  Main loop            : 0.36
% 3.07/1.47  Inferencing          : 0.13
% 3.07/1.47  Reduction            : 0.11
% 3.07/1.47  Demodulation         : 0.07
% 3.07/1.47  BG Simplification    : 0.02
% 3.07/1.47  Subsumption          : 0.08
% 3.07/1.47  Abstraction          : 0.02
% 3.07/1.47  MUC search           : 0.00
% 3.07/1.47  Cooper               : 0.00
% 3.07/1.47  Total                : 0.71
% 3.07/1.47  Index Insertion      : 0.00
% 3.07/1.47  Index Deletion       : 0.00
% 3.07/1.47  Index Matching       : 0.00
% 3.07/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
