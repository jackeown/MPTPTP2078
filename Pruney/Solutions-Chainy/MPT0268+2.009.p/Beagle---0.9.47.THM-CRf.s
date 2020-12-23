%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:35 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 119 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 143 expanded)
%              Number of equality atoms :   44 (  74 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_34,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    ! [A_58] : k3_xboole_0(k1_xboole_0,A_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_141])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_58] : k3_xboole_0(A_58,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2])).

tff(c_277,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_286,plain,(
    ! [A_58] : k5_xboole_0(A_58,k1_xboole_0) = k4_xboole_0(A_58,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_277])).

tff(c_301,plain,(
    ! [A_58] : k5_xboole_0(A_58,k1_xboole_0) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_286])).

tff(c_371,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_397,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_371])).

tff(c_403,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_397])).

tff(c_272,plain,(
    ! [A_71,B_72] :
      ( r1_xboole_0(k1_tarski(A_71),B_72)
      | r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_569,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(k1_tarski(A_110),B_111) = k1_tarski(A_110)
      | r2_hidden(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_272,c_38])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_585,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(k1_tarski(A_110),k1_tarski(A_110)) = k3_xboole_0(k1_tarski(A_110),B_111)
      | r2_hidden(A_110,B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_36])).

tff(c_616,plain,(
    ! [A_112,B_113] :
      ( k3_xboole_0(k1_tarski(A_112),B_113) = k1_xboole_0
      | r2_hidden(A_112,B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_585])).

tff(c_298,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_277])).

tff(c_628,plain,(
    ! [B_113,A_112] :
      ( k4_xboole_0(B_113,k1_tarski(A_112)) = k5_xboole_0(B_113,k1_xboole_0)
      | r2_hidden(A_112,B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_298])).

tff(c_673,plain,(
    ! [B_114,A_115] :
      ( k4_xboole_0(B_114,k1_tarski(A_115)) = B_114
      | r2_hidden(A_115,B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_628])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_237,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_700,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_237])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_700])).

tff(c_725,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_66,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_736,plain,(
    ! [A_118,B_119] : k1_enumset1(A_118,A_118,B_119) = k2_tarski(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ! [E_27,B_22,C_23] : r2_hidden(E_27,k1_enumset1(E_27,B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_754,plain,(
    ! [A_120,B_121] : r2_hidden(A_120,k2_tarski(A_120,B_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_48])).

tff(c_757,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_754])).

tff(c_726,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_759,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_80])).

tff(c_849,plain,(
    ! [D_135,B_136,A_137] :
      ( ~ r2_hidden(D_135,B_136)
      | ~ r2_hidden(D_135,k4_xboole_0(A_137,B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_866,plain,(
    ! [D_140] :
      ( ~ r2_hidden(D_140,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_140,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_849])).

tff(c_870,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_757,c_866])).

tff(c_874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_870])).

tff(c_875,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1026,plain,(
    ! [A_163,B_164] : k1_enumset1(A_163,A_163,B_164) = k2_tarski(A_163,B_164) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1044,plain,(
    ! [A_165,B_166] : r2_hidden(A_165,k2_tarski(A_165,B_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_48])).

tff(c_1047,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1044])).

tff(c_876,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_913,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_82])).

tff(c_1118,plain,(
    ! [D_178,B_179,A_180] :
      ( ~ r2_hidden(D_178,B_179)
      | ~ r2_hidden(D_178,k4_xboole_0(A_180,B_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1155,plain,(
    ! [D_186] :
      ( ~ r2_hidden(D_186,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_186,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_1118])).

tff(c_1159,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1047,c_1155])).

tff(c_1163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_1159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 3.29/1.52  
% 3.29/1.52  %Foreground sorts:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Background operators:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Foreground operators:
% 3.29/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.29/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.29/1.52  
% 3.29/1.53  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.29/1.53  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.29/1.53  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.29/1.53  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.29/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.29/1.53  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.29/1.53  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.29/1.53  tff(f_87, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.29/1.53  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.29/1.53  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/1.53  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.29/1.53  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.29/1.53  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.29/1.53  tff(c_78, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.53  tff(c_104, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 3.29/1.53  tff(c_34, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.53  tff(c_32, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.53  tff(c_141, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.53  tff(c_159, plain, (![A_58]: (k3_xboole_0(k1_xboole_0, A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_141])).
% 3.29/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.53  tff(c_168, plain, (![A_58]: (k3_xboole_0(A_58, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_2])).
% 3.29/1.53  tff(c_277, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.53  tff(c_286, plain, (![A_58]: (k5_xboole_0(A_58, k1_xboole_0)=k4_xboole_0(A_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_277])).
% 3.29/1.53  tff(c_301, plain, (![A_58]: (k5_xboole_0(A_58, k1_xboole_0)=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_286])).
% 3.29/1.53  tff(c_371, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.53  tff(c_397, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_371])).
% 3.29/1.53  tff(c_403, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_397])).
% 3.29/1.53  tff(c_272, plain, (![A_71, B_72]: (r1_xboole_0(k1_tarski(A_71), B_72) | r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.29/1.53  tff(c_38, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.53  tff(c_569, plain, (![A_110, B_111]: (k4_xboole_0(k1_tarski(A_110), B_111)=k1_tarski(A_110) | r2_hidden(A_110, B_111))), inference(resolution, [status(thm)], [c_272, c_38])).
% 3.29/1.53  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.53  tff(c_585, plain, (![A_110, B_111]: (k4_xboole_0(k1_tarski(A_110), k1_tarski(A_110))=k3_xboole_0(k1_tarski(A_110), B_111) | r2_hidden(A_110, B_111))), inference(superposition, [status(thm), theory('equality')], [c_569, c_36])).
% 3.29/1.53  tff(c_616, plain, (![A_112, B_113]: (k3_xboole_0(k1_tarski(A_112), B_113)=k1_xboole_0 | r2_hidden(A_112, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_585])).
% 3.29/1.53  tff(c_298, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_277])).
% 3.29/1.53  tff(c_628, plain, (![B_113, A_112]: (k4_xboole_0(B_113, k1_tarski(A_112))=k5_xboole_0(B_113, k1_xboole_0) | r2_hidden(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_616, c_298])).
% 3.29/1.53  tff(c_673, plain, (![B_114, A_115]: (k4_xboole_0(B_114, k1_tarski(A_115))=B_114 | r2_hidden(A_115, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_628])).
% 3.29/1.53  tff(c_76, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.53  tff(c_237, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_76])).
% 3.29/1.53  tff(c_700, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_673, c_237])).
% 3.29/1.53  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_700])).
% 3.29/1.53  tff(c_725, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 3.29/1.53  tff(c_66, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.53  tff(c_736, plain, (![A_118, B_119]: (k1_enumset1(A_118, A_118, B_119)=k2_tarski(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.29/1.53  tff(c_48, plain, (![E_27, B_22, C_23]: (r2_hidden(E_27, k1_enumset1(E_27, B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.29/1.53  tff(c_754, plain, (![A_120, B_121]: (r2_hidden(A_120, k2_tarski(A_120, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_736, c_48])).
% 3.29/1.53  tff(c_757, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_754])).
% 3.29/1.53  tff(c_726, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_76])).
% 3.29/1.53  tff(c_80, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.53  tff(c_759, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_726, c_80])).
% 3.29/1.53  tff(c_849, plain, (![D_135, B_136, A_137]: (~r2_hidden(D_135, B_136) | ~r2_hidden(D_135, k4_xboole_0(A_137, B_136)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.53  tff(c_866, plain, (![D_140]: (~r2_hidden(D_140, k1_tarski('#skF_8')) | ~r2_hidden(D_140, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_759, c_849])).
% 3.29/1.53  tff(c_870, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_757, c_866])).
% 3.29/1.53  tff(c_874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_725, c_870])).
% 3.29/1.53  tff(c_875, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 3.29/1.53  tff(c_1026, plain, (![A_163, B_164]: (k1_enumset1(A_163, A_163, B_164)=k2_tarski(A_163, B_164))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.29/1.53  tff(c_1044, plain, (![A_165, B_166]: (r2_hidden(A_165, k2_tarski(A_165, B_166)))), inference(superposition, [status(thm), theory('equality')], [c_1026, c_48])).
% 3.29/1.53  tff(c_1047, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1044])).
% 3.29/1.53  tff(c_876, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 3.29/1.53  tff(c_82, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.53  tff(c_913, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_876, c_82])).
% 3.29/1.53  tff(c_1118, plain, (![D_178, B_179, A_180]: (~r2_hidden(D_178, B_179) | ~r2_hidden(D_178, k4_xboole_0(A_180, B_179)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.53  tff(c_1155, plain, (![D_186]: (~r2_hidden(D_186, k1_tarski('#skF_8')) | ~r2_hidden(D_186, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_913, c_1118])).
% 3.29/1.53  tff(c_1159, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1047, c_1155])).
% 3.29/1.53  tff(c_1163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_875, c_1159])).
% 3.29/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  Inference rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Ref     : 0
% 3.29/1.53  #Sup     : 258
% 3.29/1.53  #Fact    : 0
% 3.29/1.53  #Define  : 0
% 3.29/1.53  #Split   : 2
% 3.29/1.53  #Chain   : 0
% 3.29/1.53  #Close   : 0
% 3.29/1.53  
% 3.29/1.53  Ordering : KBO
% 3.29/1.53  
% 3.29/1.53  Simplification rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Subsume      : 16
% 3.29/1.53  #Demod        : 72
% 3.29/1.53  #Tautology    : 177
% 3.29/1.53  #SimpNegUnit  : 1
% 3.29/1.53  #BackRed      : 1
% 3.29/1.53  
% 3.29/1.53  #Partial instantiations: 0
% 3.29/1.53  #Strategies tried      : 1
% 3.29/1.53  
% 3.29/1.53  Timing (in seconds)
% 3.29/1.53  ----------------------
% 3.29/1.54  Preprocessing        : 0.35
% 3.29/1.54  Parsing              : 0.17
% 3.29/1.54  CNF conversion       : 0.03
% 3.29/1.54  Main loop            : 0.39
% 3.29/1.54  Inferencing          : 0.15
% 3.29/1.54  Reduction            : 0.13
% 3.29/1.54  Demodulation         : 0.10
% 3.29/1.54  BG Simplification    : 0.02
% 3.29/1.54  Subsumption          : 0.06
% 3.29/1.54  Abstraction          : 0.02
% 3.29/1.54  MUC search           : 0.00
% 3.29/1.54  Cooper               : 0.00
% 3.29/1.54  Total                : 0.78
% 3.29/1.54  Index Insertion      : 0.00
% 3.29/1.54  Index Deletion       : 0.00
% 3.29/1.54  Index Matching       : 0.00
% 3.29/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
