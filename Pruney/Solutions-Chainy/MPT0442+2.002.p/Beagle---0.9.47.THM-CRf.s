%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:20 EST 2020

% Result     : Theorem 32.39s
% Output     : CNFRefutation 32.53s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 138 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 343 expanded)
%              Number of equality atoms :   29 (  73 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
                & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_44,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1309,plain,(
    ! [A_164,B_165,C_166] :
      ( r2_hidden('#skF_2'(A_164,B_165,C_166),B_165)
      | r2_hidden('#skF_2'(A_164,B_165,C_166),A_164)
      | r2_hidden('#skF_3'(A_164,B_165,C_166),C_166)
      | k2_xboole_0(A_164,B_165) = C_166 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8803,plain,(
    ! [A_457,B_458] :
      ( r2_hidden('#skF_2'(A_457,B_458,A_457),B_458)
      | r2_hidden('#skF_3'(A_457,B_458,A_457),A_457)
      | k2_xboole_0(A_457,B_458) = A_457 ) ),
    inference(resolution,[status(thm)],[c_1309,c_24])).

tff(c_1650,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_hidden('#skF_2'(A_179,B_180,C_181),B_180)
      | r2_hidden('#skF_2'(A_179,B_180,C_181),A_179)
      | ~ r2_hidden('#skF_3'(A_179,B_180,C_181),A_179)
      | k2_xboole_0(A_179,B_180) = C_181 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1700,plain,(
    ! [A_179,B_180] :
      ( r2_hidden('#skF_2'(A_179,B_180,A_179),B_180)
      | ~ r2_hidden('#skF_3'(A_179,B_180,A_179),A_179)
      | k2_xboole_0(A_179,B_180) = A_179 ) ),
    inference(resolution,[status(thm)],[c_1650,c_20])).

tff(c_8919,plain,(
    ! [A_459,B_460] :
      ( r2_hidden('#skF_2'(A_459,B_460,A_459),B_460)
      | k2_xboole_0(A_459,B_460) = A_459 ) ),
    inference(resolution,[status(thm)],[c_8803,c_1700])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9314,plain,(
    ! [A_469,B_470,B_471] :
      ( r2_hidden('#skF_2'(A_469,B_470,A_469),B_471)
      | ~ r1_tarski(B_470,B_471)
      | k2_xboole_0(A_469,B_470) = A_469 ) ),
    inference(resolution,[status(thm)],[c_8919,c_4])).

tff(c_10640,plain,(
    ! [B_504,B_505] :
      ( r2_hidden('#skF_3'(B_504,B_505,B_504),B_504)
      | ~ r1_tarski(B_505,B_504)
      | k2_xboole_0(B_504,B_505) = B_504 ) ),
    inference(resolution,[status(thm)],[c_9314,c_24])).

tff(c_9373,plain,(
    ! [B_471,B_470] :
      ( ~ r2_hidden('#skF_3'(B_471,B_470,B_471),B_471)
      | ~ r1_tarski(B_470,B_471)
      | k2_xboole_0(B_471,B_470) = B_471 ) ),
    inference(resolution,[status(thm)],[c_9314,c_20])).

tff(c_10693,plain,(
    ! [B_506,B_507] :
      ( ~ r1_tarski(B_506,B_507)
      | k2_xboole_0(B_507,B_506) = B_507 ) ),
    inference(resolution,[status(thm)],[c_10640,c_9373])).

tff(c_10772,plain,(
    k2_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_46,c_10693])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_265,plain,(
    ! [A_81,B_82] :
      ( k2_xboole_0(k1_relat_1(A_81),k1_relat_1(B_82)) = k1_relat_1(k2_xboole_0(A_81,B_82))
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_559,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k1_relat_1(A_111),k1_relat_1(k2_xboole_0(A_111,B_112)))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_28])).

tff(c_568,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),k1_relat_1(k2_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_559])).

tff(c_10900,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10772,c_568])).

tff(c_10967,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_10900])).

tff(c_10969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_10967])).

tff(c_10970,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_11974,plain,(
    ! [A_612,B_613,C_614] :
      ( r2_hidden('#skF_2'(A_612,B_613,C_614),B_613)
      | r2_hidden('#skF_2'(A_612,B_613,C_614),A_612)
      | r2_hidden('#skF_3'(A_612,B_613,C_614),C_614)
      | k2_xboole_0(A_612,B_613) = C_614 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17358,plain,(
    ! [A_845,B_846] :
      ( r2_hidden('#skF_2'(A_845,B_846,B_846),A_845)
      | r2_hidden('#skF_3'(A_845,B_846,B_846),B_846)
      | k2_xboole_0(A_845,B_846) = B_846 ) ),
    inference(resolution,[status(thm)],[c_11974,c_24])).

tff(c_12512,plain,(
    ! [A_637,B_638,C_639] :
      ( r2_hidden('#skF_2'(A_637,B_638,C_639),B_638)
      | r2_hidden('#skF_2'(A_637,B_638,C_639),A_637)
      | ~ r2_hidden('#skF_3'(A_637,B_638,C_639),B_638)
      | k2_xboole_0(A_637,B_638) = C_639 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),B_9)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12555,plain,(
    ! [A_637,B_638] :
      ( r2_hidden('#skF_2'(A_637,B_638,B_638),A_637)
      | ~ r2_hidden('#skF_3'(A_637,B_638,B_638),B_638)
      | k2_xboole_0(A_637,B_638) = B_638 ) ),
    inference(resolution,[status(thm)],[c_12512,c_16])).

tff(c_17441,plain,(
    ! [A_847,B_848] :
      ( r2_hidden('#skF_2'(A_847,B_848,B_848),A_847)
      | k2_xboole_0(A_847,B_848) = B_848 ) ),
    inference(resolution,[status(thm)],[c_17358,c_12555])).

tff(c_17875,plain,(
    ! [A_869,B_870,B_871] :
      ( r2_hidden('#skF_2'(A_869,B_870,B_870),B_871)
      | ~ r1_tarski(A_869,B_871)
      | k2_xboole_0(A_869,B_870) = B_870 ) ),
    inference(resolution,[status(thm)],[c_17441,c_4])).

tff(c_17915,plain,(
    ! [A_869,B_871] :
      ( r2_hidden('#skF_3'(A_869,B_871,B_871),B_871)
      | ~ r1_tarski(A_869,B_871)
      | k2_xboole_0(A_869,B_871) = B_871 ) ),
    inference(resolution,[status(thm)],[c_17875,c_24])).

tff(c_18519,plain,(
    ! [A_894,B_895] :
      ( ~ r2_hidden('#skF_3'(A_894,B_895,B_895),B_895)
      | ~ r1_tarski(A_894,B_895)
      | k2_xboole_0(A_894,B_895) = B_895 ) ),
    inference(resolution,[status(thm)],[c_17875,c_16])).

tff(c_18668,plain,(
    ! [A_896,B_897] :
      ( ~ r1_tarski(A_896,B_897)
      | k2_xboole_0(A_896,B_897) = B_897 ) ),
    inference(resolution,[status(thm)],[c_17915,c_18519])).

tff(c_18761,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_46,c_18668])).

tff(c_30,plain,(
    ! [A_16,C_31] :
      ( r2_hidden(k4_tarski('#skF_7'(A_16,k2_relat_1(A_16),C_31),C_31),A_16)
      | ~ r2_hidden(C_31,k2_relat_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11006,plain,(
    ! [C_517,A_518,D_519] :
      ( r2_hidden(C_517,k2_relat_1(A_518))
      | ~ r2_hidden(k4_tarski(D_519,C_517),A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11347,plain,(
    ! [C_559,A_560,B_561,D_562] :
      ( r2_hidden(C_559,k2_relat_1(k2_xboole_0(A_560,B_561)))
      | ~ r2_hidden(k4_tarski(D_562,C_559),B_561) ) ),
    inference(resolution,[status(thm)],[c_12,c_11006])).

tff(c_11375,plain,(
    ! [C_563,A_564,A_565] :
      ( r2_hidden(C_563,k2_relat_1(k2_xboole_0(A_564,A_565)))
      | ~ r2_hidden(C_563,k2_relat_1(A_565)) ) ),
    inference(resolution,[status(thm)],[c_30,c_11347])).

tff(c_11397,plain,(
    ! [C_563,B_2,A_1] :
      ( r2_hidden(C_563,k2_relat_1(k2_xboole_0(B_2,A_1)))
      | ~ r2_hidden(C_563,k2_relat_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11375])).

tff(c_20766,plain,(
    ! [C_915] :
      ( r2_hidden(C_915,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_915,k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18761,c_11397])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107879,plain,(
    ! [A_1666] :
      ( r1_tarski(A_1666,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_1'(A_1666,k2_relat_1('#skF_9')),k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_20766,c_6])).

tff(c_107939,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_8,c_107879])).

tff(c_107958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10970,c_10970,c_107939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:16:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.39/20.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.39/20.66  
% 32.39/20.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.39/20.66  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 32.39/20.66  
% 32.39/20.66  %Foreground sorts:
% 32.39/20.66  
% 32.39/20.66  
% 32.39/20.66  %Background operators:
% 32.39/20.66  
% 32.39/20.66  
% 32.39/20.66  %Foreground operators:
% 32.39/20.66  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 32.39/20.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.39/20.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.39/20.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 32.39/20.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.39/20.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 32.39/20.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 32.39/20.66  tff('#skF_9', type, '#skF_9': $i).
% 32.39/20.66  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 32.39/20.66  tff('#skF_8', type, '#skF_8': $i).
% 32.39/20.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.39/20.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 32.39/20.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 32.39/20.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.39/20.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 32.39/20.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 32.39/20.66  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 32.39/20.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 32.39/20.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 32.39/20.66  
% 32.53/20.67  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 32.53/20.67  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 32.53/20.67  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 32.53/20.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 32.53/20.67  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 32.53/20.67  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 32.53/20.67  tff(f_53, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 32.53/20.67  tff(c_44, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.53/20.67  tff(c_109, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_44])).
% 32.53/20.67  tff(c_50, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.53/20.67  tff(c_48, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.53/20.67  tff(c_46, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.53/20.67  tff(c_1309, plain, (![A_164, B_165, C_166]: (r2_hidden('#skF_2'(A_164, B_165, C_166), B_165) | r2_hidden('#skF_2'(A_164, B_165, C_166), A_164) | r2_hidden('#skF_3'(A_164, B_165, C_166), C_166) | k2_xboole_0(A_164, B_165)=C_166)), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_8803, plain, (![A_457, B_458]: (r2_hidden('#skF_2'(A_457, B_458, A_457), B_458) | r2_hidden('#skF_3'(A_457, B_458, A_457), A_457) | k2_xboole_0(A_457, B_458)=A_457)), inference(resolution, [status(thm)], [c_1309, c_24])).
% 32.53/20.67  tff(c_1650, plain, (![A_179, B_180, C_181]: (r2_hidden('#skF_2'(A_179, B_180, C_181), B_180) | r2_hidden('#skF_2'(A_179, B_180, C_181), A_179) | ~r2_hidden('#skF_3'(A_179, B_180, C_181), A_179) | k2_xboole_0(A_179, B_180)=C_181)), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_20, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_1700, plain, (![A_179, B_180]: (r2_hidden('#skF_2'(A_179, B_180, A_179), B_180) | ~r2_hidden('#skF_3'(A_179, B_180, A_179), A_179) | k2_xboole_0(A_179, B_180)=A_179)), inference(resolution, [status(thm)], [c_1650, c_20])).
% 32.53/20.67  tff(c_8919, plain, (![A_459, B_460]: (r2_hidden('#skF_2'(A_459, B_460, A_459), B_460) | k2_xboole_0(A_459, B_460)=A_459)), inference(resolution, [status(thm)], [c_8803, c_1700])).
% 32.53/20.67  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 32.53/20.67  tff(c_9314, plain, (![A_469, B_470, B_471]: (r2_hidden('#skF_2'(A_469, B_470, A_469), B_471) | ~r1_tarski(B_470, B_471) | k2_xboole_0(A_469, B_470)=A_469)), inference(resolution, [status(thm)], [c_8919, c_4])).
% 32.53/20.67  tff(c_10640, plain, (![B_504, B_505]: (r2_hidden('#skF_3'(B_504, B_505, B_504), B_504) | ~r1_tarski(B_505, B_504) | k2_xboole_0(B_504, B_505)=B_504)), inference(resolution, [status(thm)], [c_9314, c_24])).
% 32.53/20.67  tff(c_9373, plain, (![B_471, B_470]: (~r2_hidden('#skF_3'(B_471, B_470, B_471), B_471) | ~r1_tarski(B_470, B_471) | k2_xboole_0(B_471, B_470)=B_471)), inference(resolution, [status(thm)], [c_9314, c_20])).
% 32.53/20.67  tff(c_10693, plain, (![B_506, B_507]: (~r1_tarski(B_506, B_507) | k2_xboole_0(B_507, B_506)=B_507)), inference(resolution, [status(thm)], [c_10640, c_9373])).
% 32.53/20.67  tff(c_10772, plain, (k2_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_46, c_10693])).
% 32.53/20.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 32.53/20.67  tff(c_265, plain, (![A_81, B_82]: (k2_xboole_0(k1_relat_1(A_81), k1_relat_1(B_82))=k1_relat_1(k2_xboole_0(A_81, B_82)) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 32.53/20.67  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 32.53/20.67  tff(c_559, plain, (![A_111, B_112]: (r1_tarski(k1_relat_1(A_111), k1_relat_1(k2_xboole_0(A_111, B_112))) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_265, c_28])).
% 32.53/20.67  tff(c_568, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), k1_relat_1(k2_xboole_0(A_1, B_2))) | ~v1_relat_1(A_1) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_559])).
% 32.53/20.67  tff(c_10900, plain, (r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10772, c_568])).
% 32.53/20.67  tff(c_10967, plain, (r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_10900])).
% 32.53/20.67  tff(c_10969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_10967])).
% 32.53/20.67  tff(c_10970, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_44])).
% 32.53/20.67  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 32.53/20.67  tff(c_11974, plain, (![A_612, B_613, C_614]: (r2_hidden('#skF_2'(A_612, B_613, C_614), B_613) | r2_hidden('#skF_2'(A_612, B_613, C_614), A_612) | r2_hidden('#skF_3'(A_612, B_613, C_614), C_614) | k2_xboole_0(A_612, B_613)=C_614)), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_17358, plain, (![A_845, B_846]: (r2_hidden('#skF_2'(A_845, B_846, B_846), A_845) | r2_hidden('#skF_3'(A_845, B_846, B_846), B_846) | k2_xboole_0(A_845, B_846)=B_846)), inference(resolution, [status(thm)], [c_11974, c_24])).
% 32.53/20.67  tff(c_12512, plain, (![A_637, B_638, C_639]: (r2_hidden('#skF_2'(A_637, B_638, C_639), B_638) | r2_hidden('#skF_2'(A_637, B_638, C_639), A_637) | ~r2_hidden('#skF_3'(A_637, B_638, C_639), B_638) | k2_xboole_0(A_637, B_638)=C_639)), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_16, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), B_9) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_12555, plain, (![A_637, B_638]: (r2_hidden('#skF_2'(A_637, B_638, B_638), A_637) | ~r2_hidden('#skF_3'(A_637, B_638, B_638), B_638) | k2_xboole_0(A_637, B_638)=B_638)), inference(resolution, [status(thm)], [c_12512, c_16])).
% 32.53/20.67  tff(c_17441, plain, (![A_847, B_848]: (r2_hidden('#skF_2'(A_847, B_848, B_848), A_847) | k2_xboole_0(A_847, B_848)=B_848)), inference(resolution, [status(thm)], [c_17358, c_12555])).
% 32.53/20.67  tff(c_17875, plain, (![A_869, B_870, B_871]: (r2_hidden('#skF_2'(A_869, B_870, B_870), B_871) | ~r1_tarski(A_869, B_871) | k2_xboole_0(A_869, B_870)=B_870)), inference(resolution, [status(thm)], [c_17441, c_4])).
% 32.53/20.67  tff(c_17915, plain, (![A_869, B_871]: (r2_hidden('#skF_3'(A_869, B_871, B_871), B_871) | ~r1_tarski(A_869, B_871) | k2_xboole_0(A_869, B_871)=B_871)), inference(resolution, [status(thm)], [c_17875, c_24])).
% 32.53/20.67  tff(c_18519, plain, (![A_894, B_895]: (~r2_hidden('#skF_3'(A_894, B_895, B_895), B_895) | ~r1_tarski(A_894, B_895) | k2_xboole_0(A_894, B_895)=B_895)), inference(resolution, [status(thm)], [c_17875, c_16])).
% 32.53/20.67  tff(c_18668, plain, (![A_896, B_897]: (~r1_tarski(A_896, B_897) | k2_xboole_0(A_896, B_897)=B_897)), inference(resolution, [status(thm)], [c_17915, c_18519])).
% 32.53/20.67  tff(c_18761, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_46, c_18668])).
% 32.53/20.67  tff(c_30, plain, (![A_16, C_31]: (r2_hidden(k4_tarski('#skF_7'(A_16, k2_relat_1(A_16), C_31), C_31), A_16) | ~r2_hidden(C_31, k2_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.53/20.67  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | r2_hidden(D_13, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.53/20.67  tff(c_11006, plain, (![C_517, A_518, D_519]: (r2_hidden(C_517, k2_relat_1(A_518)) | ~r2_hidden(k4_tarski(D_519, C_517), A_518))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.53/20.67  tff(c_11347, plain, (![C_559, A_560, B_561, D_562]: (r2_hidden(C_559, k2_relat_1(k2_xboole_0(A_560, B_561))) | ~r2_hidden(k4_tarski(D_562, C_559), B_561))), inference(resolution, [status(thm)], [c_12, c_11006])).
% 32.53/20.67  tff(c_11375, plain, (![C_563, A_564, A_565]: (r2_hidden(C_563, k2_relat_1(k2_xboole_0(A_564, A_565))) | ~r2_hidden(C_563, k2_relat_1(A_565)))), inference(resolution, [status(thm)], [c_30, c_11347])).
% 32.53/20.67  tff(c_11397, plain, (![C_563, B_2, A_1]: (r2_hidden(C_563, k2_relat_1(k2_xboole_0(B_2, A_1))) | ~r2_hidden(C_563, k2_relat_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11375])).
% 32.53/20.67  tff(c_20766, plain, (![C_915]: (r2_hidden(C_915, k2_relat_1('#skF_9')) | ~r2_hidden(C_915, k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_18761, c_11397])).
% 32.53/20.67  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 32.53/20.67  tff(c_107879, plain, (![A_1666]: (r1_tarski(A_1666, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_1'(A_1666, k2_relat_1('#skF_9')), k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_20766, c_6])).
% 32.53/20.67  tff(c_107939, plain, (r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_8, c_107879])).
% 32.53/20.67  tff(c_107958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10970, c_10970, c_107939])).
% 32.53/20.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.53/20.67  
% 32.53/20.67  Inference rules
% 32.53/20.67  ----------------------
% 32.53/20.67  #Ref     : 0
% 32.53/20.67  #Sup     : 27952
% 32.53/20.67  #Fact    : 64
% 32.53/20.67  #Define  : 0
% 32.53/20.67  #Split   : 5
% 32.53/20.67  #Chain   : 0
% 32.53/20.67  #Close   : 0
% 32.53/20.67  
% 32.53/20.67  Ordering : KBO
% 32.53/20.67  
% 32.53/20.67  Simplification rules
% 32.53/20.67  ----------------------
% 32.53/20.67  #Subsume      : 6757
% 32.53/20.67  #Demod        : 17081
% 32.53/20.67  #Tautology    : 6309
% 32.53/20.67  #SimpNegUnit  : 6
% 32.53/20.67  #BackRed      : 3
% 32.53/20.67  
% 32.53/20.67  #Partial instantiations: 0
% 32.53/20.67  #Strategies tried      : 1
% 32.53/20.67  
% 32.53/20.67  Timing (in seconds)
% 32.53/20.67  ----------------------
% 32.53/20.68  Preprocessing        : 0.29
% 32.53/20.68  Parsing              : 0.15
% 32.53/20.68  CNF conversion       : 0.03
% 32.53/20.68  Main loop            : 19.64
% 32.53/20.68  Inferencing          : 2.22
% 32.53/20.68  Reduction            : 7.56
% 32.53/20.68  Demodulation         : 6.67
% 32.53/20.68  BG Simplification    : 0.33
% 32.53/20.68  Subsumption          : 8.41
% 32.53/20.68  Abstraction          : 0.44
% 32.53/20.68  MUC search           : 0.00
% 32.53/20.68  Cooper               : 0.00
% 32.53/20.68  Total                : 19.96
% 32.53/20.68  Index Insertion      : 0.00
% 32.53/20.68  Index Deletion       : 0.00
% 32.53/20.68  Index Matching       : 0.00
% 32.53/20.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
