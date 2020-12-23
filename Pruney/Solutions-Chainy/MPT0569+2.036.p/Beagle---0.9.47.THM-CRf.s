%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:40 EST 2020

% Result     : Theorem 9.76s
% Output     : CNFRefutation 9.76s
% Verified   : 
% Statistics : Number of formulae       :   70 (  98 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 183 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
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

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_52,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8')
    | k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_70,plain,(
    k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_7'(A_58,B_59,C_60),B_59)
      | ~ r2_hidden(A_58,k10_relat_1(C_60,B_59))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_526,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden('#skF_7'(A_138,B_139,C_140),k2_relat_1(C_140))
      | ~ r2_hidden(A_138,k10_relat_1(C_140,B_139))
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_58,plain,
    ( k10_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_91,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_58])).

tff(c_100,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [C_85] :
      ( ~ r2_hidden(C_85,'#skF_8')
      | ~ r2_hidden(C_85,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_91,c_100])).

tff(c_542,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden('#skF_7'(A_138,B_139,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_138,k10_relat_1('#skF_9',B_139))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_526,c_108])).

tff(c_642,plain,(
    ! [A_149,B_150] :
      ( ~ r2_hidden('#skF_7'(A_149,B_150,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_149,k10_relat_1('#skF_9',B_150)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_542])).

tff(c_646,plain,(
    ! [A_58] :
      ( ~ r2_hidden(A_58,k10_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_40,c_642])).

tff(c_650,plain,(
    ! [A_151] : ~ r2_hidden(A_151,k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_646])).

tff(c_670,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_650])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_670])).

tff(c_679,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_687,plain,(
    ! [A_152,C_153,B_154] :
      ( ~ r2_hidden(A_152,C_153)
      | ~ r1_xboole_0(k2_tarski(A_152,B_154),C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_692,plain,(
    ! [A_152] : ~ r2_hidden(A_152,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_687])).

tff(c_681,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_58])).

tff(c_26,plain,(
    ! [A_39,C_54] :
      ( r2_hidden(k4_tarski('#skF_6'(A_39,k2_relat_1(A_39),C_54),C_54),A_39)
      | ~ r2_hidden(C_54,k2_relat_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1316,plain,(
    ! [A_243,C_244,B_245,D_246] :
      ( r2_hidden(A_243,k10_relat_1(C_244,B_245))
      | ~ r2_hidden(D_246,B_245)
      | ~ r2_hidden(k4_tarski(A_243,D_246),C_244)
      | ~ r2_hidden(D_246,k2_relat_1(C_244))
      | ~ v1_relat_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4392,plain,(
    ! [A_394,C_395,A_396,B_397] :
      ( r2_hidden(A_394,k10_relat_1(C_395,A_396))
      | ~ r2_hidden(k4_tarski(A_394,'#skF_1'(A_396,B_397)),C_395)
      | ~ r2_hidden('#skF_1'(A_396,B_397),k2_relat_1(C_395))
      | ~ v1_relat_1(C_395)
      | r1_xboole_0(A_396,B_397) ) ),
    inference(resolution,[status(thm)],[c_6,c_1316])).

tff(c_9607,plain,(
    ! [A_580,A_581,B_582] :
      ( r2_hidden('#skF_6'(A_580,k2_relat_1(A_580),'#skF_1'(A_581,B_582)),k10_relat_1(A_580,A_581))
      | ~ v1_relat_1(A_580)
      | r1_xboole_0(A_581,B_582)
      | ~ r2_hidden('#skF_1'(A_581,B_582),k2_relat_1(A_580)) ) ),
    inference(resolution,[status(thm)],[c_26,c_4392])).

tff(c_9725,plain,(
    ! [B_582] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'('#skF_8',B_582)),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | r1_xboole_0('#skF_8',B_582)
      | ~ r2_hidden('#skF_1'('#skF_8',B_582),k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_9607])).

tff(c_9746,plain,(
    ! [B_582] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'('#skF_8',B_582)),k1_xboole_0)
      | r1_xboole_0('#skF_8',B_582)
      | ~ r2_hidden('#skF_1'('#skF_8',B_582),k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9725])).

tff(c_9748,plain,(
    ! [B_583] :
      ( r1_xboole_0('#skF_8',B_583)
      | ~ r2_hidden('#skF_1'('#skF_8',B_583),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_9746])).

tff(c_9753,plain,(
    r1_xboole_0('#skF_8',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_9748])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9757,plain,(
    ! [C_584] :
      ( ~ r2_hidden(C_584,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_584,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9753,c_2])).

tff(c_10001,plain,(
    ! [B_589] :
      ( ~ r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_589),'#skF_8')
      | r1_xboole_0(k2_relat_1('#skF_9'),B_589) ) ),
    inference(resolution,[status(thm)],[c_6,c_9757])).

tff(c_10005,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_10001])).

tff(c_10009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_679,c_10005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.76/3.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.23  
% 9.76/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.24  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 9.76/3.24  
% 9.76/3.24  %Foreground sorts:
% 9.76/3.24  
% 9.76/3.24  
% 9.76/3.24  %Background operators:
% 9.76/3.24  
% 9.76/3.24  
% 9.76/3.24  %Foreground operators:
% 9.76/3.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.76/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.76/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.76/3.24  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.76/3.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.76/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.76/3.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.76/3.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.76/3.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.76/3.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.76/3.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.76/3.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.76/3.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.76/3.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.76/3.24  tff('#skF_9', type, '#skF_9': $i).
% 9.76/3.24  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.76/3.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.76/3.24  tff('#skF_8', type, '#skF_8': $i).
% 9.76/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.76/3.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.76/3.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.76/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.76/3.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.76/3.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.76/3.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.76/3.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.76/3.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.76/3.24  
% 9.76/3.25  tff(f_104, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 9.76/3.25  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.76/3.25  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 9.76/3.25  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.76/3.25  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.76/3.25  tff(f_70, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 9.76/3.25  tff(f_78, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 9.76/3.25  tff(c_52, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8') | k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.76/3.25  tff(c_70, plain, (k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 9.76/3.25  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.25  tff(c_50, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.76/3.25  tff(c_40, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_7'(A_58, B_59, C_60), B_59) | ~r2_hidden(A_58, k10_relat_1(C_60, B_59)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.76/3.25  tff(c_526, plain, (![A_138, B_139, C_140]: (r2_hidden('#skF_7'(A_138, B_139, C_140), k2_relat_1(C_140)) | ~r2_hidden(A_138, k10_relat_1(C_140, B_139)) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.76/3.25  tff(c_58, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.76/3.25  tff(c_91, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_70, c_58])).
% 9.76/3.25  tff(c_100, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.76/3.25  tff(c_108, plain, (![C_85]: (~r2_hidden(C_85, '#skF_8') | ~r2_hidden(C_85, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_91, c_100])).
% 9.76/3.25  tff(c_542, plain, (![A_138, B_139]: (~r2_hidden('#skF_7'(A_138, B_139, '#skF_9'), '#skF_8') | ~r2_hidden(A_138, k10_relat_1('#skF_9', B_139)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_526, c_108])).
% 9.76/3.25  tff(c_642, plain, (![A_149, B_150]: (~r2_hidden('#skF_7'(A_149, B_150, '#skF_9'), '#skF_8') | ~r2_hidden(A_149, k10_relat_1('#skF_9', B_150)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_542])).
% 9.76/3.25  tff(c_646, plain, (![A_58]: (~r2_hidden(A_58, k10_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_40, c_642])).
% 9.76/3.25  tff(c_650, plain, (![A_151]: (~r2_hidden(A_151, k10_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_646])).
% 9.76/3.25  tff(c_670, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_650])).
% 9.76/3.25  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_670])).
% 9.76/3.25  tff(c_679, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 9.76/3.25  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.76/3.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.76/3.25  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.76/3.25  tff(c_687, plain, (![A_152, C_153, B_154]: (~r2_hidden(A_152, C_153) | ~r1_xboole_0(k2_tarski(A_152, B_154), C_153))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.76/3.25  tff(c_692, plain, (![A_152]: (~r2_hidden(A_152, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_687])).
% 9.76/3.25  tff(c_681, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_679, c_58])).
% 9.76/3.25  tff(c_26, plain, (![A_39, C_54]: (r2_hidden(k4_tarski('#skF_6'(A_39, k2_relat_1(A_39), C_54), C_54), A_39) | ~r2_hidden(C_54, k2_relat_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.76/3.25  tff(c_1316, plain, (![A_243, C_244, B_245, D_246]: (r2_hidden(A_243, k10_relat_1(C_244, B_245)) | ~r2_hidden(D_246, B_245) | ~r2_hidden(k4_tarski(A_243, D_246), C_244) | ~r2_hidden(D_246, k2_relat_1(C_244)) | ~v1_relat_1(C_244))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.76/3.25  tff(c_4392, plain, (![A_394, C_395, A_396, B_397]: (r2_hidden(A_394, k10_relat_1(C_395, A_396)) | ~r2_hidden(k4_tarski(A_394, '#skF_1'(A_396, B_397)), C_395) | ~r2_hidden('#skF_1'(A_396, B_397), k2_relat_1(C_395)) | ~v1_relat_1(C_395) | r1_xboole_0(A_396, B_397))), inference(resolution, [status(thm)], [c_6, c_1316])).
% 9.76/3.25  tff(c_9607, plain, (![A_580, A_581, B_582]: (r2_hidden('#skF_6'(A_580, k2_relat_1(A_580), '#skF_1'(A_581, B_582)), k10_relat_1(A_580, A_581)) | ~v1_relat_1(A_580) | r1_xboole_0(A_581, B_582) | ~r2_hidden('#skF_1'(A_581, B_582), k2_relat_1(A_580)))), inference(resolution, [status(thm)], [c_26, c_4392])).
% 9.76/3.25  tff(c_9725, plain, (![B_582]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'('#skF_8', B_582)), k1_xboole_0) | ~v1_relat_1('#skF_9') | r1_xboole_0('#skF_8', B_582) | ~r2_hidden('#skF_1'('#skF_8', B_582), k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_681, c_9607])).
% 9.76/3.25  tff(c_9746, plain, (![B_582]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'('#skF_8', B_582)), k1_xboole_0) | r1_xboole_0('#skF_8', B_582) | ~r2_hidden('#skF_1'('#skF_8', B_582), k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_9725])).
% 9.76/3.25  tff(c_9748, plain, (![B_583]: (r1_xboole_0('#skF_8', B_583) | ~r2_hidden('#skF_1'('#skF_8', B_583), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_692, c_9746])).
% 9.76/3.25  tff(c_9753, plain, (r1_xboole_0('#skF_8', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_4, c_9748])).
% 9.76/3.25  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.76/3.25  tff(c_9757, plain, (![C_584]: (~r2_hidden(C_584, k2_relat_1('#skF_9')) | ~r2_hidden(C_584, '#skF_8'))), inference(resolution, [status(thm)], [c_9753, c_2])).
% 9.76/3.25  tff(c_10001, plain, (![B_589]: (~r2_hidden('#skF_1'(k2_relat_1('#skF_9'), B_589), '#skF_8') | r1_xboole_0(k2_relat_1('#skF_9'), B_589))), inference(resolution, [status(thm)], [c_6, c_9757])).
% 9.76/3.25  tff(c_10005, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_4, c_10001])).
% 9.76/3.25  tff(c_10009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_679, c_679, c_10005])).
% 9.76/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.25  
% 9.76/3.25  Inference rules
% 9.76/3.25  ----------------------
% 9.76/3.25  #Ref     : 0
% 9.76/3.25  #Sup     : 2451
% 9.76/3.25  #Fact    : 0
% 9.76/3.25  #Define  : 0
% 9.76/3.25  #Split   : 14
% 9.76/3.25  #Chain   : 0
% 9.76/3.25  #Close   : 0
% 9.76/3.25  
% 9.76/3.25  Ordering : KBO
% 9.76/3.25  
% 9.76/3.25  Simplification rules
% 9.76/3.25  ----------------------
% 9.76/3.25  #Subsume      : 1288
% 9.76/3.25  #Demod        : 1277
% 9.76/3.25  #Tautology    : 429
% 9.76/3.25  #SimpNegUnit  : 120
% 9.76/3.25  #BackRed      : 2
% 9.76/3.25  
% 9.76/3.25  #Partial instantiations: 0
% 9.76/3.25  #Strategies tried      : 1
% 9.76/3.25  
% 9.76/3.25  Timing (in seconds)
% 9.76/3.25  ----------------------
% 9.76/3.25  Preprocessing        : 0.36
% 9.76/3.25  Parsing              : 0.19
% 9.76/3.25  CNF conversion       : 0.03
% 9.76/3.25  Main loop            : 2.11
% 9.76/3.25  Inferencing          : 0.56
% 9.76/3.25  Reduction            : 0.44
% 9.76/3.25  Demodulation         : 0.30
% 9.76/3.25  BG Simplification    : 0.05
% 9.76/3.25  Subsumption          : 0.95
% 9.76/3.25  Abstraction          : 0.08
% 9.76/3.25  MUC search           : 0.00
% 9.76/3.25  Cooper               : 0.00
% 9.76/3.25  Total                : 2.50
% 9.76/3.25  Index Insertion      : 0.00
% 9.76/3.25  Index Deletion       : 0.00
% 9.76/3.25  Index Matching       : 0.00
% 9.76/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
