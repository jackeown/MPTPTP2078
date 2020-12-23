%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:07 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 115 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 172 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(k3_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_339,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),B_86)
      | r1_xboole_0(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_185,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = k1_xboole_0
      | ~ r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_185])).

tff(c_246,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_252,plain,(
    ! [C_83] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_246])).

tff(c_262,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_252])).

tff(c_348,plain,(
    ! [A_85] : r1_xboole_0(A_85,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_339,c_262])).

tff(c_1993,plain,(
    ! [A_149,B_150,C_151] :
      ( ~ r1_xboole_0(A_149,k3_xboole_0(B_150,C_151))
      | ~ r1_tarski(A_149,C_151)
      | r1_xboole_0(A_149,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2054,plain,(
    ! [A_149] :
      ( ~ r1_xboole_0(A_149,k1_xboole_0)
      | ~ r1_tarski(A_149,'#skF_4')
      | r1_xboole_0(A_149,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_1993])).

tff(c_2106,plain,(
    ! [A_153] :
      ( ~ r1_tarski(A_153,'#skF_4')
      | r1_xboole_0(A_153,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_2054])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2241,plain,(
    ! [A_165] :
      ( k3_xboole_0(A_165,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_165,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2106,c_4])).

tff(c_2606,plain,(
    ! [B_184] : k3_xboole_0(k3_xboole_0('#skF_4',B_184),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_2241])).

tff(c_2718,plain,(
    ! [B_184] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',B_184)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2606])).

tff(c_176,plain,(
    ! [A_77,B_78] :
      ( r1_xboole_0(A_77,B_78)
      | k3_xboole_0(A_77,B_78) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_182,plain,(
    ! [B_78,A_77] :
      ( r1_xboole_0(B_78,A_77)
      | k3_xboole_0(A_77,B_78) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_176,c_8])).

tff(c_64,plain,(
    ! [B_62,A_63] :
      ( r1_xboole_0(B_62,A_63)
      | ~ r1_xboole_0(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_200,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_185])).

tff(c_1672,plain,(
    ! [A_144,B_145,C_146] :
      ( k3_xboole_0(A_144,k2_xboole_0(B_145,C_146)) = k3_xboole_0(A_144,C_146)
      | ~ r1_xboole_0(A_144,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_181,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_176,c_46])).

tff(c_184,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_1738,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1672,c_184])).

tff(c_1789,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1738])).

tff(c_1798,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_1789])).

tff(c_1803,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1798])).

tff(c_42,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(k1_tarski(A_55),B_56)
      | r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_945,plain,(
    ! [A_118,B_119] :
      ( k3_xboole_0(k1_tarski(A_118),B_119) = k1_xboole_0
      | r2_hidden(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_42,c_185])).

tff(c_1120,plain,(
    ! [A_125,A_126] :
      ( k3_xboole_0(A_125,k1_tarski(A_126)) = k1_xboole_0
      | r2_hidden(A_126,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_945])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_111,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_118,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_111])).

tff(c_1165,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_118])).

tff(c_2211,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1803,c_1165])).

tff(c_50,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_850,plain,(
    ! [A_110,B_111,C_112] :
      ( ~ r1_xboole_0(A_110,B_111)
      | ~ r2_hidden(C_112,B_111)
      | ~ r2_hidden(C_112,A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3224,plain,(
    ! [C_193,B_194,A_195] :
      ( ~ r2_hidden(C_193,B_194)
      | ~ r2_hidden(C_193,A_195)
      | k3_xboole_0(A_195,B_194) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_850])).

tff(c_3246,plain,(
    ! [A_196] :
      ( ~ r2_hidden('#skF_6',A_196)
      | k3_xboole_0(A_196,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_3224])).

tff(c_3249,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2211,c_3246])).

tff(c_3256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2718,c_2,c_3249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.82  
% 4.54/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.54/1.82  
% 4.54/1.82  %Foreground sorts:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Background operators:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Foreground operators:
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.54/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.54/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.54/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.54/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.82  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.54/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.54/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.54/1.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.54/1.82  
% 4.54/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.54/1.83  tff(f_69, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.54/1.83  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.54/1.83  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.54/1.83  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.54/1.83  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.54/1.83  tff(f_81, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.54/1.83  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.54/1.83  tff(f_85, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.54/1.83  tff(f_104, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.54/1.83  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.54/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.54/1.83  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k3_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.54/1.83  tff(c_339, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), B_86) | r1_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.83  tff(c_48, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.54/1.83  tff(c_185, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=k1_xboole_0 | ~r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.83  tff(c_201, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_185])).
% 4.54/1.83  tff(c_246, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.54/1.83  tff(c_252, plain, (![C_83]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_201, c_246])).
% 4.54/1.83  tff(c_262, plain, (![C_83]: (~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_252])).
% 4.54/1.83  tff(c_348, plain, (![A_85]: (r1_xboole_0(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_339, c_262])).
% 4.54/1.83  tff(c_1993, plain, (![A_149, B_150, C_151]: (~r1_xboole_0(A_149, k3_xboole_0(B_150, C_151)) | ~r1_tarski(A_149, C_151) | r1_xboole_0(A_149, B_150))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.54/1.83  tff(c_2054, plain, (![A_149]: (~r1_xboole_0(A_149, k1_xboole_0) | ~r1_tarski(A_149, '#skF_4') | r1_xboole_0(A_149, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_1993])).
% 4.54/1.83  tff(c_2106, plain, (![A_153]: (~r1_tarski(A_153, '#skF_4') | r1_xboole_0(A_153, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_2054])).
% 4.54/1.83  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.83  tff(c_2241, plain, (![A_165]: (k3_xboole_0(A_165, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_165, '#skF_4'))), inference(resolution, [status(thm)], [c_2106, c_4])).
% 4.54/1.83  tff(c_2606, plain, (![B_184]: (k3_xboole_0(k3_xboole_0('#skF_4', B_184), '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_2241])).
% 4.54/1.83  tff(c_2718, plain, (![B_184]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', B_184))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2606])).
% 4.54/1.83  tff(c_176, plain, (![A_77, B_78]: (r1_xboole_0(A_77, B_78) | k3_xboole_0(A_77, B_78)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.83  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.54/1.83  tff(c_182, plain, (![B_78, A_77]: (r1_xboole_0(B_78, A_77) | k3_xboole_0(A_77, B_78)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_176, c_8])).
% 4.54/1.83  tff(c_64, plain, (![B_62, A_63]: (r1_xboole_0(B_62, A_63) | ~r1_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.54/1.83  tff(c_67, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_64])).
% 4.54/1.83  tff(c_200, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_67, c_185])).
% 4.54/1.83  tff(c_1672, plain, (![A_144, B_145, C_146]: (k3_xboole_0(A_144, k2_xboole_0(B_145, C_146))=k3_xboole_0(A_144, C_146) | ~r1_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.54/1.83  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.54/1.83  tff(c_181, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_176, c_46])).
% 4.54/1.83  tff(c_184, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_181])).
% 4.54/1.83  tff(c_1738, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1672, c_184])).
% 4.54/1.83  tff(c_1789, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1738])).
% 4.54/1.83  tff(c_1798, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_1789])).
% 4.54/1.83  tff(c_1803, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1798])).
% 4.54/1.83  tff(c_42, plain, (![A_55, B_56]: (r1_xboole_0(k1_tarski(A_55), B_56) | r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.54/1.83  tff(c_945, plain, (![A_118, B_119]: (k3_xboole_0(k1_tarski(A_118), B_119)=k1_xboole_0 | r2_hidden(A_118, B_119))), inference(resolution, [status(thm)], [c_42, c_185])).
% 4.54/1.83  tff(c_1120, plain, (![A_125, A_126]: (k3_xboole_0(A_125, k1_tarski(A_126))=k1_xboole_0 | r2_hidden(A_126, A_125))), inference(superposition, [status(thm), theory('equality')], [c_2, c_945])).
% 4.54/1.83  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.54/1.83  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 4.54/1.83  tff(c_111, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.54/1.83  tff(c_118, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_53, c_111])).
% 4.54/1.83  tff(c_1165, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1120, c_118])).
% 4.54/1.83  tff(c_2211, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1803, c_1165])).
% 4.54/1.83  tff(c_50, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.54/1.83  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.83  tff(c_850, plain, (![A_110, B_111, C_112]: (~r1_xboole_0(A_110, B_111) | ~r2_hidden(C_112, B_111) | ~r2_hidden(C_112, A_110))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.83  tff(c_3224, plain, (![C_193, B_194, A_195]: (~r2_hidden(C_193, B_194) | ~r2_hidden(C_193, A_195) | k3_xboole_0(A_195, B_194)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_850])).
% 4.54/1.83  tff(c_3246, plain, (![A_196]: (~r2_hidden('#skF_6', A_196) | k3_xboole_0(A_196, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_3224])).
% 4.54/1.83  tff(c_3249, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2211, c_3246])).
% 4.54/1.83  tff(c_3256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2718, c_2, c_3249])).
% 4.54/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.83  
% 4.54/1.83  Inference rules
% 4.54/1.83  ----------------------
% 4.54/1.83  #Ref     : 0
% 4.54/1.83  #Sup     : 794
% 4.54/1.83  #Fact    : 0
% 4.54/1.83  #Define  : 0
% 4.54/1.83  #Split   : 3
% 4.54/1.83  #Chain   : 0
% 4.54/1.83  #Close   : 0
% 4.54/1.83  
% 4.54/1.83  Ordering : KBO
% 4.54/1.83  
% 4.54/1.83  Simplification rules
% 4.54/1.83  ----------------------
% 4.54/1.83  #Subsume      : 107
% 4.54/1.83  #Demod        : 553
% 4.54/1.83  #Tautology    : 431
% 4.54/1.83  #SimpNegUnit  : 27
% 4.54/1.83  #BackRed      : 0
% 4.54/1.83  
% 4.54/1.83  #Partial instantiations: 0
% 4.54/1.83  #Strategies tried      : 1
% 4.54/1.83  
% 4.54/1.83  Timing (in seconds)
% 4.54/1.83  ----------------------
% 4.54/1.84  Preprocessing        : 0.34
% 4.54/1.84  Parsing              : 0.18
% 4.54/1.84  CNF conversion       : 0.03
% 4.54/1.84  Main loop            : 0.73
% 4.54/1.84  Inferencing          : 0.22
% 4.54/1.84  Reduction            : 0.30
% 4.54/1.84  Demodulation         : 0.23
% 4.54/1.84  BG Simplification    : 0.03
% 4.54/1.84  Subsumption          : 0.13
% 4.54/1.84  Abstraction          : 0.03
% 4.54/1.84  MUC search           : 0.00
% 4.54/1.84  Cooper               : 0.00
% 4.54/1.84  Total                : 1.10
% 4.54/1.84  Index Insertion      : 0.00
% 4.54/1.84  Index Deletion       : 0.00
% 4.54/1.84  Index Matching       : 0.00
% 4.54/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
