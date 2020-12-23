%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:25 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 121 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 191 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_4 > #skF_14 > #skF_10 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_123,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(c_66,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_64,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_60,plain,(
    v2_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_62,plain,(
    r1_xboole_0('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_92,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(A_103,B_104) = k1_xboole_0
      | ~ r1_xboole_0(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    k3_xboole_0('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_92])).

tff(c_1126,plain,(
    ! [C_211,A_212,B_213] :
      ( k3_xboole_0(k9_relat_1(C_211,A_212),k9_relat_1(C_211,B_213)) = k9_relat_1(C_211,k3_xboole_0(A_212,B_213))
      | ~ v2_funct_1(C_211)
      | ~ v1_funct_1(C_211)
      | ~ v1_relat_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_14','#skF_12'),k9_relat_1('#skF_14','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_85,plain,(
    k3_xboole_0(k9_relat_1('#skF_14','#skF_12'),k9_relat_1('#skF_14','#skF_13')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_1173,plain,
    ( k9_relat_1('#skF_14',k3_xboole_0('#skF_12','#skF_13')) != k1_xboole_0
    | ~ v2_funct_1('#skF_14')
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_1126,c_85])).

tff(c_1187,plain,(
    k9_relat_1('#skF_14',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_104,c_1173])).

tff(c_44,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_7'(A_60),A_60)
      | v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    ! [A_100,B_101] :
      ( ~ r2_hidden(A_100,B_101)
      | ~ r1_xboole_0(k1_tarski(A_100),B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    ! [A_102] : ~ r2_hidden(A_102,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_952,plain,(
    ! [A_196,B_197,D_198] :
      ( r2_hidden(k4_tarski('#skF_6'(A_196,B_197,k9_relat_1(A_196,B_197),D_198),D_198),A_196)
      | ~ r2_hidden(D_198,k9_relat_1(A_196,B_197))
      | ~ v1_relat_1(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_81,plain,(
    ! [A_100] : ~ r2_hidden(A_100,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_972,plain,(
    ! [D_198,B_197] :
      ( ~ r2_hidden(D_198,k9_relat_1(k1_xboole_0,B_197))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_952,c_81])).

tff(c_984,plain,(
    ! [D_199,B_200] : ~ r2_hidden(D_199,k9_relat_1(k1_xboole_0,B_200)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_972])).

tff(c_1020,plain,(
    ! [B_200] : v1_relat_1(k9_relat_1(k1_xboole_0,B_200)) ),
    inference(resolution,[status(thm)],[c_44,c_984])).

tff(c_54,plain,(
    ! [A_87] :
      ( k1_xboole_0 = A_87
      | r2_hidden(k4_tarski('#skF_10'(A_87),'#skF_11'(A_87)),A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1015,plain,(
    ! [B_200] :
      ( k9_relat_1(k1_xboole_0,B_200) = k1_xboole_0
      | ~ v1_relat_1(k9_relat_1(k1_xboole_0,B_200)) ) ),
    inference(resolution,[status(thm)],[c_54,c_984])).

tff(c_1754,plain,(
    ! [B_200] : k9_relat_1(k1_xboole_0,B_200) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1015])).

tff(c_2113,plain,(
    ! [A_235,B_236,C_237] :
      ( r2_hidden(k4_tarski('#skF_4'(A_235,B_236,C_237),'#skF_3'(A_235,B_236,C_237)),A_235)
      | r2_hidden('#skF_5'(A_235,B_236,C_237),C_237)
      | k9_relat_1(A_235,B_236) = C_237
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2133,plain,(
    ! [B_236,C_237] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_236,C_237),C_237)
      | k9_relat_1(k1_xboole_0,B_236) = C_237
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2113,c_81])).

tff(c_2142,plain,(
    ! [B_238,C_239] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_238,C_239),C_239)
      | k1_xboole_0 = C_239 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1754,c_2133])).

tff(c_851,plain,(
    ! [A_184,B_185,D_186] :
      ( r2_hidden('#skF_6'(A_184,B_185,k9_relat_1(A_184,B_185),D_186),B_185)
      | ~ r2_hidden(D_186,k9_relat_1(A_184,B_185))
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_875,plain,(
    ! [D_186,A_184] :
      ( ~ r2_hidden(D_186,k9_relat_1(A_184,k1_xboole_0))
      | ~ v1_relat_1(A_184) ) ),
    inference(resolution,[status(thm)],[c_851,c_81])).

tff(c_2170,plain,(
    ! [A_240] :
      ( ~ v1_relat_1(A_240)
      | k9_relat_1(A_240,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2142,c_875])).

tff(c_2182,plain,(
    k9_relat_1('#skF_14',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_2170])).

tff(c_2190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_2182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.72  
% 3.91/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.72  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_4 > #skF_14 > #skF_10 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_1 > #skF_9 > #skF_12
% 3.91/1.72  
% 3.91/1.72  %Foreground sorts:
% 3.91/1.72  
% 3.91/1.72  
% 3.91/1.72  %Background operators:
% 3.91/1.72  
% 3.91/1.72  
% 3.91/1.72  %Foreground operators:
% 3.91/1.72  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.91/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.91/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.91/1.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.91/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.91/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.72  tff('#skF_14', type, '#skF_14': $i).
% 3.91/1.72  tff('#skF_10', type, '#skF_10': $i > $i).
% 3.91/1.72  tff('#skF_13', type, '#skF_13': $i).
% 3.91/1.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.91/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.91/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.91/1.72  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.91/1.72  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.91/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.72  tff('#skF_11', type, '#skF_11': $i > $i).
% 3.91/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.91/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.91/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.72  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.91/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.72  tff('#skF_12', type, '#skF_12': $i).
% 3.91/1.72  
% 3.91/1.73  tff(f_142, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 3.91/1.73  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.91/1.73  tff(f_131, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 3.91/1.73  tff(f_97, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.91/1.73  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.91/1.73  tff(f_74, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.91/1.73  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 3.91/1.73  tff(f_123, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 3.91/1.73  tff(c_66, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.91/1.73  tff(c_64, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.91/1.73  tff(c_60, plain, (v2_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.91/1.73  tff(c_62, plain, (r1_xboole_0('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.91/1.73  tff(c_92, plain, (![A_103, B_104]: (k3_xboole_0(A_103, B_104)=k1_xboole_0 | ~r1_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.91/1.73  tff(c_104, plain, (k3_xboole_0('#skF_12', '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_92])).
% 3.91/1.73  tff(c_1126, plain, (![C_211, A_212, B_213]: (k3_xboole_0(k9_relat_1(C_211, A_212), k9_relat_1(C_211, B_213))=k9_relat_1(C_211, k3_xboole_0(A_212, B_213)) | ~v2_funct_1(C_211) | ~v1_funct_1(C_211) | ~v1_relat_1(C_211))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.91/1.73  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.91/1.73  tff(c_58, plain, (~r1_xboole_0(k9_relat_1('#skF_14', '#skF_12'), k9_relat_1('#skF_14', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.91/1.73  tff(c_85, plain, (k3_xboole_0(k9_relat_1('#skF_14', '#skF_12'), k9_relat_1('#skF_14', '#skF_13'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_58])).
% 3.91/1.73  tff(c_1173, plain, (k9_relat_1('#skF_14', k3_xboole_0('#skF_12', '#skF_13'))!=k1_xboole_0 | ~v2_funct_1('#skF_14') | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_1126, c_85])).
% 3.91/1.73  tff(c_1187, plain, (k9_relat_1('#skF_14', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_104, c_1173])).
% 3.91/1.73  tff(c_44, plain, (![A_60]: (r2_hidden('#skF_7'(A_60), A_60) | v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.91/1.73  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.91/1.73  tff(c_71, plain, (![A_100, B_101]: (~r2_hidden(A_100, B_101) | ~r1_xboole_0(k1_tarski(A_100), B_101))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.73  tff(c_86, plain, (![A_102]: (~r2_hidden(A_102, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_71])).
% 3.91/1.73  tff(c_91, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_86])).
% 3.91/1.73  tff(c_952, plain, (![A_196, B_197, D_198]: (r2_hidden(k4_tarski('#skF_6'(A_196, B_197, k9_relat_1(A_196, B_197), D_198), D_198), A_196) | ~r2_hidden(D_198, k9_relat_1(A_196, B_197)) | ~v1_relat_1(A_196))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.91/1.73  tff(c_81, plain, (![A_100]: (~r2_hidden(A_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_71])).
% 3.91/1.73  tff(c_972, plain, (![D_198, B_197]: (~r2_hidden(D_198, k9_relat_1(k1_xboole_0, B_197)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_952, c_81])).
% 3.91/1.73  tff(c_984, plain, (![D_199, B_200]: (~r2_hidden(D_199, k9_relat_1(k1_xboole_0, B_200)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_972])).
% 3.91/1.73  tff(c_1020, plain, (![B_200]: (v1_relat_1(k9_relat_1(k1_xboole_0, B_200)))), inference(resolution, [status(thm)], [c_44, c_984])).
% 3.91/1.73  tff(c_54, plain, (![A_87]: (k1_xboole_0=A_87 | r2_hidden(k4_tarski('#skF_10'(A_87), '#skF_11'(A_87)), A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.91/1.73  tff(c_1015, plain, (![B_200]: (k9_relat_1(k1_xboole_0, B_200)=k1_xboole_0 | ~v1_relat_1(k9_relat_1(k1_xboole_0, B_200)))), inference(resolution, [status(thm)], [c_54, c_984])).
% 3.91/1.73  tff(c_1754, plain, (![B_200]: (k9_relat_1(k1_xboole_0, B_200)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1015])).
% 3.91/1.73  tff(c_2113, plain, (![A_235, B_236, C_237]: (r2_hidden(k4_tarski('#skF_4'(A_235, B_236, C_237), '#skF_3'(A_235, B_236, C_237)), A_235) | r2_hidden('#skF_5'(A_235, B_236, C_237), C_237) | k9_relat_1(A_235, B_236)=C_237 | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.91/1.73  tff(c_2133, plain, (![B_236, C_237]: (r2_hidden('#skF_5'(k1_xboole_0, B_236, C_237), C_237) | k9_relat_1(k1_xboole_0, B_236)=C_237 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2113, c_81])).
% 3.91/1.73  tff(c_2142, plain, (![B_238, C_239]: (r2_hidden('#skF_5'(k1_xboole_0, B_238, C_239), C_239) | k1_xboole_0=C_239)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1754, c_2133])).
% 3.91/1.73  tff(c_851, plain, (![A_184, B_185, D_186]: (r2_hidden('#skF_6'(A_184, B_185, k9_relat_1(A_184, B_185), D_186), B_185) | ~r2_hidden(D_186, k9_relat_1(A_184, B_185)) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.91/1.73  tff(c_875, plain, (![D_186, A_184]: (~r2_hidden(D_186, k9_relat_1(A_184, k1_xboole_0)) | ~v1_relat_1(A_184))), inference(resolution, [status(thm)], [c_851, c_81])).
% 3.91/1.73  tff(c_2170, plain, (![A_240]: (~v1_relat_1(A_240) | k9_relat_1(A_240, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2142, c_875])).
% 3.91/1.73  tff(c_2182, plain, (k9_relat_1('#skF_14', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_2170])).
% 3.91/1.73  tff(c_2190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1187, c_2182])).
% 3.91/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.73  
% 3.91/1.73  Inference rules
% 3.91/1.73  ----------------------
% 3.91/1.73  #Ref     : 1
% 3.91/1.73  #Sup     : 461
% 3.91/1.73  #Fact    : 0
% 3.91/1.73  #Define  : 0
% 3.91/1.73  #Split   : 2
% 3.91/1.73  #Chain   : 0
% 3.91/1.73  #Close   : 0
% 3.91/1.74  
% 3.91/1.74  Ordering : KBO
% 3.91/1.74  
% 3.91/1.74  Simplification rules
% 3.91/1.74  ----------------------
% 3.91/1.74  #Subsume      : 93
% 3.91/1.74  #Demod        : 290
% 3.91/1.74  #Tautology    : 240
% 3.91/1.74  #SimpNegUnit  : 14
% 3.91/1.74  #BackRed      : 12
% 3.91/1.74  
% 3.91/1.74  #Partial instantiations: 0
% 3.91/1.74  #Strategies tried      : 1
% 3.91/1.74  
% 3.91/1.74  Timing (in seconds)
% 3.91/1.74  ----------------------
% 3.91/1.74  Preprocessing        : 0.36
% 3.91/1.74  Parsing              : 0.20
% 3.91/1.74  CNF conversion       : 0.03
% 3.91/1.74  Main loop            : 0.56
% 3.91/1.74  Inferencing          : 0.21
% 3.91/1.74  Reduction            : 0.17
% 3.91/1.74  Demodulation         : 0.12
% 3.91/1.74  BG Simplification    : 0.03
% 3.91/1.74  Subsumption          : 0.11
% 3.91/1.74  Abstraction          : 0.03
% 3.91/1.74  MUC search           : 0.00
% 3.91/1.74  Cooper               : 0.00
% 3.91/1.74  Total                : 0.96
% 3.91/1.74  Index Insertion      : 0.00
% 3.91/1.74  Index Deletion       : 0.00
% 3.91/1.74  Index Matching       : 0.00
% 3.91/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
