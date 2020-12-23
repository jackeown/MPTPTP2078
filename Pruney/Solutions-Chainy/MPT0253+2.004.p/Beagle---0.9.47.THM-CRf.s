%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:14 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 103 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 152 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_69,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_81,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_82,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_865,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_5'(A_126,B_127),B_127)
      | r2_hidden('#skF_6'(A_126,B_127),A_126)
      | B_127 = A_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_60,plain,(
    ! [A_25] : r1_tarski(k1_xboole_0,A_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_164,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_171,plain,(
    ! [A_25] : k3_xboole_0(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_164])).

tff(c_674,plain,(
    ! [D_93,B_94,A_95] :
      ( r2_hidden(D_93,B_94)
      | ~ r2_hidden(D_93,k3_xboole_0(A_95,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_683,plain,(
    ! [D_93,A_25] :
      ( r2_hidden(D_93,A_25)
      | ~ r2_hidden(D_93,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_674])).

tff(c_987,plain,(
    ! [B_134,A_135] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_134),A_135)
      | r2_hidden('#skF_5'(k1_xboole_0,B_134),B_134)
      | k1_xboole_0 = B_134 ) ),
    inference(resolution,[status(thm)],[c_865,c_683])).

tff(c_42,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_5'(A_15,B_16),B_16)
      | ~ r2_hidden('#skF_6'(A_15,B_16),B_16)
      | B_16 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1049,plain,(
    ! [A_136] :
      ( r2_hidden('#skF_5'(k1_xboole_0,A_136),A_136)
      | k1_xboole_0 = A_136 ) ),
    inference(resolution,[status(thm)],[c_987,c_42])).

tff(c_26,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1281,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k4_xboole_0(A_147,B_148)),A_147)
      | k4_xboole_0(A_147,B_148) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1049,c_26])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1088,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,k4_xboole_0(A_9,B_10)),B_10)
      | k4_xboole_0(A_9,B_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1049,c_24])).

tff(c_1326,plain,(
    ! [A_147] : k4_xboole_0(A_147,A_147) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1281,c_1088])).

tff(c_52,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_172,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_52,c_164])).

tff(c_394,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_406,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k4_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_394])).

tff(c_1352,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_406])).

tff(c_828,plain,(
    ! [A_117,B_118,C_119] :
      ( r1_tarski(k2_tarski(A_117,B_118),C_119)
      | ~ r2_hidden(B_118,C_119)
      | ~ r2_hidden(A_117,C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1784,plain,(
    ! [A_172,B_173,C_174] :
      ( k3_xboole_0(k2_tarski(A_172,B_173),C_174) = k2_tarski(A_172,B_173)
      | ~ r2_hidden(B_173,C_174)
      | ~ r2_hidden(A_172,C_174) ) ),
    inference(resolution,[status(thm)],[c_828,c_58])).

tff(c_54,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1814,plain,(
    ! [A_172,B_173,C_174] :
      ( k5_xboole_0(k2_tarski(A_172,B_173),k2_tarski(A_172,B_173)) = k4_xboole_0(k2_tarski(A_172,B_173),C_174)
      | ~ r2_hidden(B_173,C_174)
      | ~ r2_hidden(A_172,C_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1784,c_54])).

tff(c_1863,plain,(
    ! [A_175,B_176,C_177] :
      ( k4_xboole_0(k2_tarski(A_175,B_176),C_177) = k1_xboole_0
      | ~ r2_hidden(B_176,C_177)
      | ~ r2_hidden(A_175,C_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1814])).

tff(c_62,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1886,plain,(
    ! [C_177,A_175,B_176] :
      ( k2_xboole_0(C_177,k2_tarski(A_175,B_176)) = k2_xboole_0(C_177,k1_xboole_0)
      | ~ r2_hidden(B_176,C_177)
      | ~ r2_hidden(A_175,C_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1863,c_62])).

tff(c_2016,plain,(
    ! [C_183,A_184,B_185] :
      ( k2_xboole_0(C_183,k2_tarski(A_184,B_185)) = C_183
      | ~ r2_hidden(B_185,C_183)
      | ~ r2_hidden(A_184,C_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1886])).

tff(c_64,plain,(
    ! [B_29,A_28] : k2_tarski(B_29,A_28) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_173,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_283,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_173])).

tff(c_72,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_289,plain,(
    ! [B_61,A_60] : k2_xboole_0(B_61,A_60) = k2_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_72])).

tff(c_80,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_9'),'#skF_8') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_85,plain,(
    k2_xboole_0(k2_tarski('#skF_9','#skF_7'),'#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_80])).

tff(c_306,plain,(
    k2_xboole_0('#skF_8',k2_tarski('#skF_9','#skF_7')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_85])).

tff(c_2030,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2016,c_306])).

tff(c_2069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_2030])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:54:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.76  
% 3.36/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.76  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 3.36/1.76  
% 3.36/1.76  %Foreground sorts:
% 3.36/1.76  
% 3.36/1.76  
% 3.36/1.76  %Background operators:
% 3.36/1.76  
% 3.36/1.76  
% 3.36/1.76  %Foreground operators:
% 3.36/1.76  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.36/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.36/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.36/1.76  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.36/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.36/1.76  tff('#skF_9', type, '#skF_9': $i).
% 3.36/1.76  tff('#skF_8', type, '#skF_8': $i).
% 3.36/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.36/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.36/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.76  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.36/1.76  
% 3.36/1.77  tff(f_94, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 3.36/1.77  tff(f_63, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.36/1.77  tff(f_53, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.36/1.77  tff(f_69, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.77  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.36/1.77  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.36/1.77  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.36/1.77  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.77  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.36/1.77  tff(f_87, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.36/1.77  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.36/1.77  tff(f_73, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.36/1.77  tff(f_81, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.36/1.77  tff(c_82, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.77  tff(c_84, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.77  tff(c_56, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.77  tff(c_865, plain, (![A_126, B_127]: (r2_hidden('#skF_5'(A_126, B_127), B_127) | r2_hidden('#skF_6'(A_126, B_127), A_126) | B_127=A_126)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.77  tff(c_60, plain, (![A_25]: (r1_tarski(k1_xboole_0, A_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.36/1.77  tff(c_164, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.77  tff(c_171, plain, (![A_25]: (k3_xboole_0(k1_xboole_0, A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_164])).
% 3.36/1.77  tff(c_674, plain, (![D_93, B_94, A_95]: (r2_hidden(D_93, B_94) | ~r2_hidden(D_93, k3_xboole_0(A_95, B_94)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.77  tff(c_683, plain, (![D_93, A_25]: (r2_hidden(D_93, A_25) | ~r2_hidden(D_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_674])).
% 3.36/1.77  tff(c_987, plain, (![B_134, A_135]: (r2_hidden('#skF_6'(k1_xboole_0, B_134), A_135) | r2_hidden('#skF_5'(k1_xboole_0, B_134), B_134) | k1_xboole_0=B_134)), inference(resolution, [status(thm)], [c_865, c_683])).
% 3.36/1.77  tff(c_42, plain, (![A_15, B_16]: (r2_hidden('#skF_5'(A_15, B_16), B_16) | ~r2_hidden('#skF_6'(A_15, B_16), B_16) | B_16=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.77  tff(c_1049, plain, (![A_136]: (r2_hidden('#skF_5'(k1_xboole_0, A_136), A_136) | k1_xboole_0=A_136)), inference(resolution, [status(thm)], [c_987, c_42])).
% 3.36/1.77  tff(c_26, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, A_9) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.77  tff(c_1281, plain, (![A_147, B_148]: (r2_hidden('#skF_5'(k1_xboole_0, k4_xboole_0(A_147, B_148)), A_147) | k4_xboole_0(A_147, B_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1049, c_26])).
% 3.36/1.77  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.77  tff(c_1088, plain, (![A_9, B_10]: (~r2_hidden('#skF_5'(k1_xboole_0, k4_xboole_0(A_9, B_10)), B_10) | k4_xboole_0(A_9, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1049, c_24])).
% 3.36/1.77  tff(c_1326, plain, (![A_147]: (k4_xboole_0(A_147, A_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1281, c_1088])).
% 3.36/1.77  tff(c_52, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.36/1.77  tff(c_172, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_52, c_164])).
% 3.36/1.77  tff(c_394, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.77  tff(c_406, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k4_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_172, c_394])).
% 3.36/1.77  tff(c_1352, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_406])).
% 3.36/1.77  tff(c_828, plain, (![A_117, B_118, C_119]: (r1_tarski(k2_tarski(A_117, B_118), C_119) | ~r2_hidden(B_118, C_119) | ~r2_hidden(A_117, C_119))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.77  tff(c_58, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.77  tff(c_1784, plain, (![A_172, B_173, C_174]: (k3_xboole_0(k2_tarski(A_172, B_173), C_174)=k2_tarski(A_172, B_173) | ~r2_hidden(B_173, C_174) | ~r2_hidden(A_172, C_174))), inference(resolution, [status(thm)], [c_828, c_58])).
% 3.36/1.77  tff(c_54, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.77  tff(c_1814, plain, (![A_172, B_173, C_174]: (k5_xboole_0(k2_tarski(A_172, B_173), k2_tarski(A_172, B_173))=k4_xboole_0(k2_tarski(A_172, B_173), C_174) | ~r2_hidden(B_173, C_174) | ~r2_hidden(A_172, C_174))), inference(superposition, [status(thm), theory('equality')], [c_1784, c_54])).
% 3.36/1.77  tff(c_1863, plain, (![A_175, B_176, C_177]: (k4_xboole_0(k2_tarski(A_175, B_176), C_177)=k1_xboole_0 | ~r2_hidden(B_176, C_177) | ~r2_hidden(A_175, C_177))), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1814])).
% 3.36/1.77  tff(c_62, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.36/1.77  tff(c_1886, plain, (![C_177, A_175, B_176]: (k2_xboole_0(C_177, k2_tarski(A_175, B_176))=k2_xboole_0(C_177, k1_xboole_0) | ~r2_hidden(B_176, C_177) | ~r2_hidden(A_175, C_177))), inference(superposition, [status(thm), theory('equality')], [c_1863, c_62])).
% 3.36/1.77  tff(c_2016, plain, (![C_183, A_184, B_185]: (k2_xboole_0(C_183, k2_tarski(A_184, B_185))=C_183 | ~r2_hidden(B_185, C_183) | ~r2_hidden(A_184, C_183))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1886])).
% 3.36/1.77  tff(c_64, plain, (![B_29, A_28]: (k2_tarski(B_29, A_28)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.36/1.77  tff(c_173, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.77  tff(c_283, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(B_61, A_60))), inference(superposition, [status(thm), theory('equality')], [c_64, c_173])).
% 3.36/1.77  tff(c_72, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.77  tff(c_289, plain, (![B_61, A_60]: (k2_xboole_0(B_61, A_60)=k2_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_283, c_72])).
% 3.36/1.77  tff(c_80, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_9'), '#skF_8')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.77  tff(c_85, plain, (k2_xboole_0(k2_tarski('#skF_9', '#skF_7'), '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_80])).
% 3.36/1.77  tff(c_306, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_9', '#skF_7'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_85])).
% 3.36/1.77  tff(c_2030, plain, (~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2016, c_306])).
% 3.36/1.77  tff(c_2069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_84, c_2030])).
% 3.36/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.77  
% 3.36/1.77  Inference rules
% 3.36/1.77  ----------------------
% 3.36/1.77  #Ref     : 0
% 3.36/1.77  #Sup     : 448
% 3.36/1.77  #Fact    : 0
% 3.36/1.77  #Define  : 0
% 3.36/1.77  #Split   : 0
% 3.36/1.77  #Chain   : 0
% 3.36/1.77  #Close   : 0
% 3.36/1.77  
% 3.36/1.77  Ordering : KBO
% 3.36/1.77  
% 3.36/1.77  Simplification rules
% 3.36/1.77  ----------------------
% 3.36/1.77  #Subsume      : 76
% 3.36/1.77  #Demod        : 170
% 3.36/1.77  #Tautology    : 215
% 3.36/1.77  #SimpNegUnit  : 0
% 3.36/1.77  #BackRed      : 4
% 3.36/1.77  
% 3.36/1.77  #Partial instantiations: 0
% 3.36/1.77  #Strategies tried      : 1
% 3.36/1.77  
% 3.36/1.77  Timing (in seconds)
% 3.36/1.77  ----------------------
% 3.36/1.78  Preprocessing        : 0.39
% 3.36/1.78  Parsing              : 0.21
% 3.36/1.78  CNF conversion       : 0.03
% 3.36/1.78  Main loop            : 0.51
% 3.36/1.78  Inferencing          : 0.17
% 3.36/1.78  Reduction            : 0.18
% 3.36/1.78  Demodulation         : 0.14
% 3.36/1.78  BG Simplification    : 0.03
% 3.36/1.78  Subsumption          : 0.10
% 3.36/1.78  Abstraction          : 0.03
% 3.36/1.78  MUC search           : 0.00
% 3.36/1.78  Cooper               : 0.00
% 3.36/1.78  Total                : 0.93
% 3.36/1.78  Index Insertion      : 0.00
% 3.36/1.78  Index Deletion       : 0.00
% 3.36/1.78  Index Matching       : 0.00
% 3.36/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
