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
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 101 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 139 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
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

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(k3_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_178,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_198,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_178])).

tff(c_1110,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,k3_xboole_0(B_115,C_116))
      | ~ r1_tarski(A_114,C_116)
      | r1_xboole_0(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1139,plain,(
    ! [A_114] :
      ( ~ r1_xboole_0(A_114,k1_xboole_0)
      | ~ r1_tarski(A_114,'#skF_4')
      | r1_xboole_0(A_114,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_1110])).

tff(c_1172,plain,(
    ! [A_117] :
      ( ~ r1_tarski(A_117,'#skF_4')
      | r1_xboole_0(A_117,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1139])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1394,plain,(
    ! [A_128] :
      ( k3_xboole_0(A_128,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_128,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1172,c_6])).

tff(c_1938,plain,(
    ! [B_142] : k3_xboole_0(k3_xboole_0('#skF_4',B_142),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_1394])).

tff(c_2015,plain,(
    ! [B_142] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',B_142)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1938])).

tff(c_303,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_313,plain,(
    ! [B_65,A_64] :
      ( r1_xboole_0(B_65,A_64)
      | k3_xboole_0(A_64,B_65) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_303,c_10])).

tff(c_250,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_198])).

tff(c_1255,plain,(
    ! [A_124,B_125,C_126] :
      ( k3_xboole_0(A_124,k2_xboole_0(B_125,C_126)) = k3_xboole_0(A_124,C_126)
      | ~ r1_xboole_0(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_311,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_303,c_44])).

tff(c_315,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_311])).

tff(c_1301,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_315])).

tff(c_1348,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_1301])).

tff(c_1364,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_313,c_1348])).

tff(c_1371,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1364])).

tff(c_42,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1713,plain,(
    ! [A_137,B_138] :
      ( k3_xboole_0(k1_tarski(A_137),B_138) = k1_xboole_0
      | r2_hidden(A_137,B_138) ) ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_51,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_165,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_176,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_165])).

tff(c_384,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_176])).

tff(c_1771,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1713,c_384])).

tff(c_1827,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1371,c_1771])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_630,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,B_93)
      | ~ r2_hidden(C_94,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1922,plain,(
    ! [C_139,B_140,A_141] :
      ( ~ r2_hidden(C_139,B_140)
      | ~ r2_hidden(C_139,A_141)
      | k3_xboole_0(A_141,B_140) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_630])).

tff(c_2148,plain,(
    ! [A_144] :
      ( ~ r2_hidden('#skF_6',A_144)
      | k3_xboole_0(A_144,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_1922])).

tff(c_2151,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1827,c_2148])).

tff(c_2156,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2151])).

tff(c_2234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_2156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.63  
% 3.42/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.74/1.63  
% 3.74/1.63  %Foreground sorts:
% 3.74/1.63  
% 3.74/1.63  
% 3.74/1.63  %Background operators:
% 3.74/1.63  
% 3.74/1.63  
% 3.74/1.63  %Foreground operators:
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.74/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.74/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/1.63  
% 3.74/1.64  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.74/1.64  tff(f_73, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.74/1.64  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.74/1.64  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.74/1.64  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.74/1.64  tff(f_87, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.74/1.64  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.74/1.64  tff(f_91, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.74/1.64  tff(f_104, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.74/1.64  tff(f_77, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.74/1.64  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.74/1.64  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.74/1.64  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(k3_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.74/1.64  tff(c_28, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.74/1.64  tff(c_46, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.74/1.64  tff(c_178, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.64  tff(c_198, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_178])).
% 3.74/1.64  tff(c_1110, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, k3_xboole_0(B_115, C_116)) | ~r1_tarski(A_114, C_116) | r1_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.74/1.64  tff(c_1139, plain, (![A_114]: (~r1_xboole_0(A_114, k1_xboole_0) | ~r1_tarski(A_114, '#skF_4') | r1_xboole_0(A_114, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_198, c_1110])).
% 3.74/1.64  tff(c_1172, plain, (![A_117]: (~r1_tarski(A_117, '#skF_4') | r1_xboole_0(A_117, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1139])).
% 3.74/1.64  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.64  tff(c_1394, plain, (![A_128]: (k3_xboole_0(A_128, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_128, '#skF_4'))), inference(resolution, [status(thm)], [c_1172, c_6])).
% 3.74/1.64  tff(c_1938, plain, (![B_142]: (k3_xboole_0(k3_xboole_0('#skF_4', B_142), '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_1394])).
% 3.74/1.64  tff(c_2015, plain, (![B_142]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', B_142))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1938])).
% 3.74/1.64  tff(c_303, plain, (![A_64, B_65]: (r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.64  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.64  tff(c_313, plain, (![B_65, A_64]: (r1_xboole_0(B_65, A_64) | k3_xboole_0(A_64, B_65)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_303, c_10])).
% 3.74/1.64  tff(c_250, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_198])).
% 3.74/1.64  tff(c_1255, plain, (![A_124, B_125, C_126]: (k3_xboole_0(A_124, k2_xboole_0(B_125, C_126))=k3_xboole_0(A_124, C_126) | ~r1_xboole_0(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.64  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.74/1.64  tff(c_311, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_303, c_44])).
% 3.74/1.64  tff(c_315, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_311])).
% 3.74/1.64  tff(c_1301, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1255, c_315])).
% 3.74/1.64  tff(c_1348, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_1301])).
% 3.74/1.64  tff(c_1364, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_313, c_1348])).
% 3.74/1.64  tff(c_1371, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1364])).
% 3.74/1.64  tff(c_42, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.74/1.64  tff(c_1713, plain, (![A_137, B_138]: (k3_xboole_0(k1_tarski(A_137), B_138)=k1_xboole_0 | r2_hidden(A_137, B_138))), inference(resolution, [status(thm)], [c_42, c_178])).
% 3.74/1.64  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.74/1.64  tff(c_51, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_50])).
% 3.74/1.64  tff(c_165, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.74/1.64  tff(c_176, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_165])).
% 3.74/1.64  tff(c_384, plain, (k3_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_176])).
% 3.74/1.64  tff(c_1771, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1713, c_384])).
% 3.74/1.64  tff(c_1827, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1371, c_1771])).
% 3.74/1.64  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.74/1.64  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.64  tff(c_630, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, B_93) | ~r2_hidden(C_94, A_92))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.74/1.64  tff(c_1922, plain, (![C_139, B_140, A_141]: (~r2_hidden(C_139, B_140) | ~r2_hidden(C_139, A_141) | k3_xboole_0(A_141, B_140)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_630])).
% 3.74/1.64  tff(c_2148, plain, (![A_144]: (~r2_hidden('#skF_6', A_144) | k3_xboole_0(A_144, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_1922])).
% 3.74/1.64  tff(c_2151, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1827, c_2148])).
% 3.74/1.64  tff(c_2156, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2151])).
% 3.74/1.64  tff(c_2234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2015, c_2156])).
% 3.74/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  Inference rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Ref     : 0
% 3.74/1.64  #Sup     : 555
% 3.74/1.64  #Fact    : 0
% 3.74/1.64  #Define  : 0
% 3.74/1.64  #Split   : 2
% 3.74/1.64  #Chain   : 0
% 3.74/1.64  #Close   : 0
% 3.74/1.64  
% 3.74/1.64  Ordering : KBO
% 3.74/1.64  
% 3.74/1.64  Simplification rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Subsume      : 75
% 3.74/1.64  #Demod        : 294
% 3.74/1.64  #Tautology    : 263
% 3.74/1.64  #SimpNegUnit  : 22
% 3.74/1.64  #BackRed      : 1
% 3.74/1.64  
% 3.74/1.64  #Partial instantiations: 0
% 3.74/1.64  #Strategies tried      : 1
% 3.74/1.64  
% 3.74/1.64  Timing (in seconds)
% 3.74/1.64  ----------------------
% 3.74/1.65  Preprocessing        : 0.32
% 3.74/1.65  Parsing              : 0.17
% 3.74/1.65  CNF conversion       : 0.02
% 3.74/1.65  Main loop            : 0.56
% 3.74/1.65  Inferencing          : 0.17
% 3.74/1.65  Reduction            : 0.23
% 3.74/1.65  Demodulation         : 0.18
% 3.74/1.65  BG Simplification    : 0.02
% 3.74/1.65  Subsumption          : 0.10
% 3.74/1.65  Abstraction          : 0.03
% 3.74/1.65  MUC search           : 0.00
% 3.74/1.65  Cooper               : 0.00
% 3.74/1.65  Total                : 0.90
% 3.74/1.65  Index Insertion      : 0.00
% 3.74/1.65  Index Deletion       : 0.00
% 3.74/1.65  Index Matching       : 0.00
% 3.74/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
