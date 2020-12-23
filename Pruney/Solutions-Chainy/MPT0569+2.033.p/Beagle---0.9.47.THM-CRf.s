%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:40 EST 2020

% Result     : Theorem 10.89s
% Output     : CNFRefutation 10.89s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 134 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 243 expanded)
%              Number of equality atoms :   18 (  66 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_50,axiom,(
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

tff(c_52,plain,
    ( k10_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_90,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9')
    | k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_91,plain,(
    k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_148,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_61)
      | r2_hidden('#skF_2'(A_60,B_61),A_60)
      | B_61 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,(
    ! [A_40,B_41] : ~ r2_hidden(A_40,k2_zfmisc_1(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_75])).

tff(c_165,plain,(
    ! [B_61] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_61),B_61)
      | k1_xboole_0 = B_61 ) ),
    inference(resolution,[status(thm)],[c_148,c_81])).

tff(c_422,plain,(
    ! [A_94,C_95] :
      ( r2_hidden(k4_tarski('#skF_7'(A_94,k2_relat_1(A_94),C_95),C_95),A_94)
      | ~ r2_hidden(C_95,k2_relat_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_447,plain,(
    ! [C_96] : ~ r2_hidden(C_96,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_422,c_81])).

tff(c_493,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_447])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_494,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1,k2_relat_1(k1_xboole_0)),A_1)
      | k2_relat_1(k1_xboole_0) = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_447])).

tff(c_667,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1,k1_xboole_0),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_493,c_494])).

tff(c_44,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden('#skF_8'(A_32,B_33,C_34),B_33)
      | ~ r2_hidden(A_32,k10_relat_1(C_34,B_33))
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_509,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_8'(A_97,B_98,C_99),k2_relat_1(C_99))
      | ~ r2_hidden(A_97,k10_relat_1(C_99,B_98))
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_110,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,B_52)
      | ~ r2_hidden(C_53,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [C_53] :
      ( ~ r2_hidden(C_53,'#skF_9')
      | ~ r2_hidden(C_53,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_90,c_110])).

tff(c_513,plain,(
    ! [A_97,B_98] :
      ( ~ r2_hidden('#skF_8'(A_97,B_98,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_97,k10_relat_1('#skF_10',B_98))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_509,c_118])).

tff(c_997,plain,(
    ! [A_131,B_132] :
      ( ~ r2_hidden('#skF_8'(A_131,B_132,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_131,k10_relat_1('#skF_10',B_132)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_513])).

tff(c_1001,plain,(
    ! [A_32] :
      ( ~ r2_hidden(A_32,k10_relat_1('#skF_10','#skF_9'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_38,c_997])).

tff(c_1005,plain,(
    ! [A_133] : ~ r2_hidden(A_133,k10_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1001])).

tff(c_1009,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_667,c_1005])).

tff(c_1057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_1009])).

tff(c_1058,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1058])).

tff(c_1066,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1073,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_46])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_13,C_28] :
      ( r2_hidden(k4_tarski('#skF_7'(A_13,k2_relat_1(A_13),C_28),C_28),A_13)
      | ~ r2_hidden(C_28,k2_relat_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1817,plain,(
    ! [A_206,C_207,B_208,D_209] :
      ( r2_hidden(A_206,k10_relat_1(C_207,B_208))
      | ~ r2_hidden(D_209,B_208)
      | ~ r2_hidden(k4_tarski(A_206,D_209),C_207)
      | ~ r2_hidden(D_209,k2_relat_1(C_207))
      | ~ v1_relat_1(C_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2836,plain,(
    ! [A_267,C_268,B_269,A_270] :
      ( r2_hidden(A_267,k10_relat_1(C_268,B_269))
      | ~ r2_hidden(k4_tarski(A_267,'#skF_3'(A_270,B_269)),C_268)
      | ~ r2_hidden('#skF_3'(A_270,B_269),k2_relat_1(C_268))
      | ~ v1_relat_1(C_268)
      | r1_xboole_0(A_270,B_269) ) ),
    inference(resolution,[status(thm)],[c_12,c_1817])).

tff(c_17140,plain,(
    ! [A_4465,A_4466,B_4467] :
      ( r2_hidden('#skF_7'(A_4465,k2_relat_1(A_4465),'#skF_3'(A_4466,B_4467)),k10_relat_1(A_4465,B_4467))
      | ~ v1_relat_1(A_4465)
      | r1_xboole_0(A_4466,B_4467)
      | ~ r2_hidden('#skF_3'(A_4466,B_4467),k2_relat_1(A_4465)) ) ),
    inference(resolution,[status(thm)],[c_24,c_2836])).

tff(c_17336,plain,(
    ! [A_4466] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_3'(A_4466,'#skF_9')),k1_xboole_0)
      | ~ v1_relat_1('#skF_10')
      | r1_xboole_0(A_4466,'#skF_9')
      | ~ r2_hidden('#skF_3'(A_4466,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1066,c_17140])).

tff(c_17358,plain,(
    ! [A_4466] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_3'(A_4466,'#skF_9')),k1_xboole_0)
      | r1_xboole_0(A_4466,'#skF_9')
      | ~ r2_hidden('#skF_3'(A_4466,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_17336])).

tff(c_17360,plain,(
    ! [A_4493] :
      ( r1_xboole_0(A_4493,'#skF_9')
      | ~ r2_hidden('#skF_3'(A_4493,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_17358])).

tff(c_17367,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_14,c_17360])).

tff(c_17371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1073,c_1073,c_17367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.89/4.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.23  
% 10.89/4.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.23  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 10.89/4.23  
% 10.89/4.23  %Foreground sorts:
% 10.89/4.23  
% 10.89/4.23  
% 10.89/4.23  %Background operators:
% 10.89/4.23  
% 10.89/4.23  
% 10.89/4.23  %Foreground operators:
% 10.89/4.23  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.89/4.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.89/4.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.89/4.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.89/4.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.89/4.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.89/4.23  tff('#skF_10', type, '#skF_10': $i).
% 10.89/4.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.89/4.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.89/4.23  tff('#skF_9', type, '#skF_9': $i).
% 10.89/4.23  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 10.89/4.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.89/4.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.89/4.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.89/4.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.89/4.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.89/4.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.89/4.23  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 10.89/4.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.89/4.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.89/4.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.89/4.23  
% 10.89/4.24  tff(f_85, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 10.89/4.24  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 10.89/4.24  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.89/4.24  tff(f_59, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 10.89/4.24  tff(f_67, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 10.89/4.24  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 10.89/4.24  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.89/4.24  tff(c_52, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.89/4.24  tff(c_90, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_52])).
% 10.89/4.24  tff(c_46, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9') | k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.89/4.24  tff(c_91, plain, (k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 10.89/4.24  tff(c_148, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), B_61) | r2_hidden('#skF_2'(A_60, B_61), A_60) | B_61=A_60)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.89/4.24  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.89/4.24  tff(c_75, plain, (![A_40, B_41]: (~r2_hidden(A_40, k2_zfmisc_1(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.89/4.24  tff(c_81, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_75])).
% 10.89/4.24  tff(c_165, plain, (![B_61]: (r2_hidden('#skF_1'(k1_xboole_0, B_61), B_61) | k1_xboole_0=B_61)), inference(resolution, [status(thm)], [c_148, c_81])).
% 10.89/4.24  tff(c_422, plain, (![A_94, C_95]: (r2_hidden(k4_tarski('#skF_7'(A_94, k2_relat_1(A_94), C_95), C_95), A_94) | ~r2_hidden(C_95, k2_relat_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.89/4.24  tff(c_447, plain, (![C_96]: (~r2_hidden(C_96, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_422, c_81])).
% 10.89/4.24  tff(c_493, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_165, c_447])).
% 10.89/4.24  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.89/4.24  tff(c_494, plain, (![A_1]: (r2_hidden('#skF_2'(A_1, k2_relat_1(k1_xboole_0)), A_1) | k2_relat_1(k1_xboole_0)=A_1)), inference(resolution, [status(thm)], [c_8, c_447])).
% 10.89/4.24  tff(c_667, plain, (![A_1]: (r2_hidden('#skF_2'(A_1, k1_xboole_0), A_1) | k1_xboole_0=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_493, c_493, c_494])).
% 10.89/4.24  tff(c_44, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.89/4.24  tff(c_38, plain, (![A_32, B_33, C_34]: (r2_hidden('#skF_8'(A_32, B_33, C_34), B_33) | ~r2_hidden(A_32, k10_relat_1(C_34, B_33)) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.89/4.24  tff(c_509, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_8'(A_97, B_98, C_99), k2_relat_1(C_99)) | ~r2_hidden(A_97, k10_relat_1(C_99, B_98)) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.89/4.24  tff(c_110, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, B_52) | ~r2_hidden(C_53, A_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.89/4.24  tff(c_118, plain, (![C_53]: (~r2_hidden(C_53, '#skF_9') | ~r2_hidden(C_53, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_90, c_110])).
% 10.89/4.24  tff(c_513, plain, (![A_97, B_98]: (~r2_hidden('#skF_8'(A_97, B_98, '#skF_10'), '#skF_9') | ~r2_hidden(A_97, k10_relat_1('#skF_10', B_98)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_509, c_118])).
% 10.89/4.24  tff(c_997, plain, (![A_131, B_132]: (~r2_hidden('#skF_8'(A_131, B_132, '#skF_10'), '#skF_9') | ~r2_hidden(A_131, k10_relat_1('#skF_10', B_132)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_513])).
% 10.89/4.24  tff(c_1001, plain, (![A_32]: (~r2_hidden(A_32, k10_relat_1('#skF_10', '#skF_9')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_38, c_997])).
% 10.89/4.24  tff(c_1005, plain, (![A_133]: (~r2_hidden(A_133, k10_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1001])).
% 10.89/4.24  tff(c_1009, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_667, c_1005])).
% 10.89/4.24  tff(c_1057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_1009])).
% 10.89/4.24  tff(c_1058, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_46])).
% 10.89/4.24  tff(c_1065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_1058])).
% 10.89/4.24  tff(c_1066, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 10.89/4.24  tff(c_1073, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_46])).
% 10.89/4.24  tff(c_14, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.89/4.24  tff(c_24, plain, (![A_13, C_28]: (r2_hidden(k4_tarski('#skF_7'(A_13, k2_relat_1(A_13), C_28), C_28), A_13) | ~r2_hidden(C_28, k2_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.89/4.24  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.89/4.24  tff(c_1817, plain, (![A_206, C_207, B_208, D_209]: (r2_hidden(A_206, k10_relat_1(C_207, B_208)) | ~r2_hidden(D_209, B_208) | ~r2_hidden(k4_tarski(A_206, D_209), C_207) | ~r2_hidden(D_209, k2_relat_1(C_207)) | ~v1_relat_1(C_207))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.89/4.24  tff(c_2836, plain, (![A_267, C_268, B_269, A_270]: (r2_hidden(A_267, k10_relat_1(C_268, B_269)) | ~r2_hidden(k4_tarski(A_267, '#skF_3'(A_270, B_269)), C_268) | ~r2_hidden('#skF_3'(A_270, B_269), k2_relat_1(C_268)) | ~v1_relat_1(C_268) | r1_xboole_0(A_270, B_269))), inference(resolution, [status(thm)], [c_12, c_1817])).
% 10.89/4.24  tff(c_17140, plain, (![A_4465, A_4466, B_4467]: (r2_hidden('#skF_7'(A_4465, k2_relat_1(A_4465), '#skF_3'(A_4466, B_4467)), k10_relat_1(A_4465, B_4467)) | ~v1_relat_1(A_4465) | r1_xboole_0(A_4466, B_4467) | ~r2_hidden('#skF_3'(A_4466, B_4467), k2_relat_1(A_4465)))), inference(resolution, [status(thm)], [c_24, c_2836])).
% 10.89/4.24  tff(c_17336, plain, (![A_4466]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_3'(A_4466, '#skF_9')), k1_xboole_0) | ~v1_relat_1('#skF_10') | r1_xboole_0(A_4466, '#skF_9') | ~r2_hidden('#skF_3'(A_4466, '#skF_9'), k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_1066, c_17140])).
% 10.89/4.24  tff(c_17358, plain, (![A_4466]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_3'(A_4466, '#skF_9')), k1_xboole_0) | r1_xboole_0(A_4466, '#skF_9') | ~r2_hidden('#skF_3'(A_4466, '#skF_9'), k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_17336])).
% 10.89/4.24  tff(c_17360, plain, (![A_4493]: (r1_xboole_0(A_4493, '#skF_9') | ~r2_hidden('#skF_3'(A_4493, '#skF_9'), k2_relat_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_81, c_17358])).
% 10.89/4.24  tff(c_17367, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_14, c_17360])).
% 10.89/4.24  tff(c_17371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1073, c_1073, c_17367])).
% 10.89/4.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.24  
% 10.89/4.24  Inference rules
% 10.89/4.24  ----------------------
% 10.89/4.24  #Ref     : 0
% 10.89/4.24  #Sup     : 3467
% 10.89/4.24  #Fact    : 0
% 10.89/4.24  #Define  : 0
% 10.89/4.24  #Split   : 10
% 10.89/4.24  #Chain   : 0
% 10.89/4.24  #Close   : 0
% 10.89/4.24  
% 10.89/4.24  Ordering : KBO
% 10.89/4.24  
% 10.89/4.24  Simplification rules
% 10.89/4.24  ----------------------
% 10.89/4.24  #Subsume      : 1372
% 10.89/4.24  #Demod        : 1280
% 10.89/4.24  #Tautology    : 443
% 10.89/4.24  #SimpNegUnit  : 165
% 10.89/4.24  #BackRed      : 3
% 10.89/4.24  
% 10.89/4.24  #Partial instantiations: 2385
% 10.89/4.24  #Strategies tried      : 1
% 10.89/4.24  
% 10.89/4.24  Timing (in seconds)
% 10.89/4.24  ----------------------
% 10.89/4.24  Preprocessing        : 0.28
% 10.89/4.24  Parsing              : 0.15
% 10.89/4.24  CNF conversion       : 0.03
% 10.89/4.24  Main loop            : 3.15
% 10.89/4.25  Inferencing          : 0.63
% 10.89/4.25  Reduction            : 0.50
% 10.89/4.25  Demodulation         : 0.31
% 10.89/4.25  BG Simplification    : 0.07
% 10.89/4.25  Subsumption          : 1.84
% 10.89/4.25  Abstraction          : 0.08
% 10.89/4.25  MUC search           : 0.00
% 10.89/4.25  Cooper               : 0.00
% 10.89/4.25  Total                : 3.46
% 10.89/4.25  Index Insertion      : 0.00
% 10.89/4.25  Index Deletion       : 0.00
% 10.89/4.25  Index Matching       : 0.00
% 10.89/4.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
