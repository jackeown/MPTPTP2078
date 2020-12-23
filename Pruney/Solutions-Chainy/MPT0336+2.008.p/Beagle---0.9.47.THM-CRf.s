%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:01 EST 2020

% Result     : Theorem 5.53s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 149 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 244 expanded)
%              Number of equality atoms :   24 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_80,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_54,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_151,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_158,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_151])).

tff(c_4550,plain,(
    ! [A_219,B_220,C_221] :
      ( k3_xboole_0(A_219,k2_xboole_0(B_220,C_221)) = k3_xboole_0(A_219,C_221)
      | ~ r1_xboole_0(A_219,B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(A_54,B_55)
      | k3_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_197,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189,c_52])).

tff(c_201,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_197])).

tff(c_4584,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4550,c_201])).

tff(c_4620,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_4584])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_3'(A_15,B_16),k3_xboole_0(A_15,B_16))
      | r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_184,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_188,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_184])).

tff(c_247,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_4])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r1_xboole_0(B_14,A_13)
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_199,plain,(
    ! [B_55,A_54] :
      ( r1_xboole_0(B_55,A_54)
      | k3_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_189,c_28])).

tff(c_514,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,k3_xboole_0(A_72,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_535,plain,(
    ! [C_74] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7'))
      | ~ r2_hidden(C_74,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_514])).

tff(c_1303,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_1308,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_199,c_1303])).

tff(c_1313,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_1308])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1218,plain,(
    ! [A_111,C_112,B_113] :
      ( r1_xboole_0(k2_tarski(A_111,C_112),B_113)
      | r2_hidden(C_112,B_113)
      | r2_hidden(A_111,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4450,plain,(
    ! [A_215,B_216] :
      ( r1_xboole_0(k1_tarski(A_215),B_216)
      | r2_hidden(A_215,B_216)
      | r2_hidden(A_215,B_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1218])).

tff(c_202,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | r1_xboole_0(A_56,k3_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_219,plain,(
    ! [A_56,B_4,A_3] :
      ( ~ r1_xboole_0(A_56,B_4)
      | r1_xboole_0(A_56,k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_850,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,k3_xboole_0(B_96,A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_514])).

tff(c_871,plain,(
    ! [C_97] :
      ( ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(C_97,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_850])).

tff(c_1451,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_871])).

tff(c_1468,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_219,c_1451])).

tff(c_4491,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_4450,c_1468])).

tff(c_159,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_541,plain,(
    ! [C_74] :
      ( ~ r1_xboole_0('#skF_6','#skF_5')
      | ~ r2_hidden(C_74,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_514])).

tff(c_561,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_541])).

tff(c_1500,plain,(
    ! [D_120,A_121,B_122] :
      ( r2_hidden(D_120,k3_xboole_0(A_121,B_122))
      | ~ r2_hidden(D_120,B_122)
      | ~ r2_hidden(D_120,A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1537,plain,(
    ! [D_120] :
      ( r2_hidden(D_120,k1_xboole_0)
      | ~ r2_hidden(D_120,'#skF_5')
      | ~ r2_hidden(D_120,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_1500])).

tff(c_1552,plain,(
    ! [D_120] :
      ( ~ r2_hidden(D_120,'#skF_5')
      | ~ r2_hidden(D_120,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_561,c_1537])).

tff(c_4497,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_4491,c_1552])).

tff(c_4501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4497])).

tff(c_4504,plain,(
    ! [C_217] : ~ r2_hidden(C_217,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_871])).

tff(c_4514,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_4504])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4521,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4514,c_24])).

tff(c_4527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1313,c_4521])).

tff(c_4532,plain,(
    ! [C_218] : ~ r2_hidden(C_218,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_4542,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_4532])).

tff(c_4549,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4542,c_28])).

tff(c_4633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4620,c_4549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:11:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.53/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.12  
% 5.66/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.66/2.13  
% 5.66/2.13  %Foreground sorts:
% 5.66/2.13  
% 5.66/2.13  
% 5.66/2.13  %Background operators:
% 5.66/2.13  
% 5.66/2.13  
% 5.66/2.13  %Foreground operators:
% 5.66/2.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.66/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.66/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.66/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.66/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.66/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.66/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.66/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.66/2.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.66/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.66/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.66/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.66/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.66/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.66/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.66/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.66/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.66/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.66/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.66/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.66/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.66/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.66/2.13  
% 5.66/2.14  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.66/2.14  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.66/2.14  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.66/2.14  tff(f_76, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 5.66/2.14  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.66/2.14  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.66/2.14  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.66/2.14  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.66/2.14  tff(f_94, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 5.66/2.14  tff(f_72, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 5.66/2.14  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.66/2.14  tff(c_54, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.66/2.14  tff(c_68, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.66/2.14  tff(c_71, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_68])).
% 5.66/2.14  tff(c_151, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.66/2.14  tff(c_158, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_151])).
% 5.66/2.14  tff(c_4550, plain, (![A_219, B_220, C_221]: (k3_xboole_0(A_219, k2_xboole_0(B_220, C_221))=k3_xboole_0(A_219, C_221) | ~r1_xboole_0(A_219, B_220))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.66/2.14  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.66/2.14  tff(c_189, plain, (![A_54, B_55]: (r1_xboole_0(A_54, B_55) | k3_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.66/2.14  tff(c_52, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.66/2.14  tff(c_197, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_189, c_52])).
% 5.66/2.14  tff(c_201, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_197])).
% 5.66/2.14  tff(c_4584, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4550, c_201])).
% 5.66/2.14  tff(c_4620, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_4584])).
% 5.66/2.14  tff(c_30, plain, (![A_15, B_16]: (r2_hidden('#skF_3'(A_15, B_16), k3_xboole_0(A_15, B_16)) | r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.66/2.14  tff(c_58, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.66/2.14  tff(c_184, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.14  tff(c_188, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_184])).
% 5.66/2.14  tff(c_247, plain, (k3_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_188, c_4])).
% 5.66/2.14  tff(c_28, plain, (![B_14, A_13]: (r1_xboole_0(B_14, A_13) | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.66/2.14  tff(c_199, plain, (![B_55, A_54]: (r1_xboole_0(B_55, A_54) | k3_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_189, c_28])).
% 5.66/2.14  tff(c_514, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, k3_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.66/2.14  tff(c_535, plain, (![C_74]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7')) | ~r2_hidden(C_74, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_514])).
% 5.66/2.14  tff(c_1303, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_535])).
% 5.66/2.14  tff(c_1308, plain, (k3_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_199, c_1303])).
% 5.66/2.14  tff(c_1313, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_247, c_1308])).
% 5.66/2.14  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.66/2.14  tff(c_44, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.66/2.14  tff(c_1218, plain, (![A_111, C_112, B_113]: (r1_xboole_0(k2_tarski(A_111, C_112), B_113) | r2_hidden(C_112, B_113) | r2_hidden(A_111, B_113))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.66/2.14  tff(c_4450, plain, (![A_215, B_216]: (r1_xboole_0(k1_tarski(A_215), B_216) | r2_hidden(A_215, B_216) | r2_hidden(A_215, B_216))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1218])).
% 5.66/2.14  tff(c_202, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | r1_xboole_0(A_56, k3_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.66/2.14  tff(c_219, plain, (![A_56, B_4, A_3]: (~r1_xboole_0(A_56, B_4) | r1_xboole_0(A_56, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_202])).
% 5.66/2.14  tff(c_850, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, k3_xboole_0(B_96, A_95)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_514])).
% 5.66/2.14  tff(c_871, plain, (![C_97]: (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(C_97, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_850])).
% 5.66/2.14  tff(c_1451, plain, (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_871])).
% 5.66/2.14  tff(c_1468, plain, (~r1_xboole_0(k1_tarski('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_219, c_1451])).
% 5.66/2.14  tff(c_4491, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_4450, c_1468])).
% 5.66/2.14  tff(c_159, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_151])).
% 5.66/2.14  tff(c_541, plain, (![C_74]: (~r1_xboole_0('#skF_6', '#skF_5') | ~r2_hidden(C_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_159, c_514])).
% 5.66/2.14  tff(c_561, plain, (![C_74]: (~r2_hidden(C_74, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_541])).
% 5.66/2.14  tff(c_1500, plain, (![D_120, A_121, B_122]: (r2_hidden(D_120, k3_xboole_0(A_121, B_122)) | ~r2_hidden(D_120, B_122) | ~r2_hidden(D_120, A_121))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.66/2.14  tff(c_1537, plain, (![D_120]: (r2_hidden(D_120, k1_xboole_0) | ~r2_hidden(D_120, '#skF_5') | ~r2_hidden(D_120, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_1500])).
% 5.66/2.14  tff(c_1552, plain, (![D_120]: (~r2_hidden(D_120, '#skF_5') | ~r2_hidden(D_120, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_561, c_1537])).
% 5.66/2.14  tff(c_4497, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_4491, c_1552])).
% 5.66/2.14  tff(c_4501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_4497])).
% 5.66/2.14  tff(c_4504, plain, (![C_217]: (~r2_hidden(C_217, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_871])).
% 5.66/2.14  tff(c_4514, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_4504])).
% 5.66/2.14  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.66/2.14  tff(c_4521, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_4514, c_24])).
% 5.66/2.14  tff(c_4527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1313, c_4521])).
% 5.66/2.14  tff(c_4532, plain, (![C_218]: (~r2_hidden(C_218, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_535])).
% 5.66/2.14  tff(c_4542, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_4532])).
% 5.66/2.14  tff(c_4549, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4542, c_28])).
% 5.66/2.14  tff(c_4633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4620, c_4549])).
% 5.66/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.14  
% 5.66/2.14  Inference rules
% 5.66/2.14  ----------------------
% 5.66/2.14  #Ref     : 0
% 5.66/2.14  #Sup     : 1128
% 5.66/2.14  #Fact    : 0
% 5.66/2.14  #Define  : 0
% 5.66/2.14  #Split   : 4
% 5.66/2.14  #Chain   : 0
% 5.66/2.14  #Close   : 0
% 5.66/2.14  
% 5.66/2.14  Ordering : KBO
% 5.66/2.14  
% 5.66/2.14  Simplification rules
% 5.66/2.14  ----------------------
% 5.66/2.14  #Subsume      : 288
% 5.66/2.14  #Demod        : 491
% 5.66/2.14  #Tautology    : 558
% 5.66/2.14  #SimpNegUnit  : 75
% 5.66/2.14  #BackRed      : 1
% 5.75/2.14  
% 5.75/2.14  #Partial instantiations: 0
% 5.75/2.14  #Strategies tried      : 1
% 5.75/2.14  
% 5.75/2.14  Timing (in seconds)
% 5.75/2.14  ----------------------
% 5.75/2.14  Preprocessing        : 0.34
% 5.75/2.15  Parsing              : 0.18
% 5.75/2.15  CNF conversion       : 0.03
% 5.75/2.15  Main loop            : 1.04
% 5.75/2.15  Inferencing          : 0.33
% 5.75/2.15  Reduction            : 0.40
% 5.75/2.15  Demodulation         : 0.30
% 5.75/2.15  BG Simplification    : 0.03
% 5.75/2.15  Subsumption          : 0.21
% 5.75/2.15  Abstraction          : 0.04
% 5.75/2.15  MUC search           : 0.00
% 5.75/2.15  Cooper               : 0.00
% 5.75/2.15  Total                : 1.41
% 5.75/2.15  Index Insertion      : 0.00
% 5.75/2.15  Index Deletion       : 0.00
% 5.75/2.15  Index Matching       : 0.00
% 5.75/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
