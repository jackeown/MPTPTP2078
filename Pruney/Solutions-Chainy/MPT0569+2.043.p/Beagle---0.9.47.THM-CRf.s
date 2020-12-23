%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:41 EST 2020

% Result     : Theorem 13.54s
% Output     : CNFRefutation 13.63s
% Verified   : 
% Statistics : Number of formulae       :   66 (  88 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 168 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_107,negated_conjecture,(
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

tff(f_92,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_46,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5')
    | k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_4'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(A_33,k10_relat_1(C_35,B_34))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_535,plain,(
    ! [A_130,B_131,C_132] :
      ( r2_hidden('#skF_4'(A_130,B_131,C_132),k2_relat_1(C_132))
      | ~ r2_hidden(A_130,k10_relat_1(C_132,B_131))
      | ~ v1_relat_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,
    ( k10_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_87,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52])).

tff(c_111,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,B_60)
      | ~ r2_hidden(C_61,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [C_61] :
      ( ~ r2_hidden(C_61,'#skF_5')
      | ~ r2_hidden(C_61,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_87,c_111])).

tff(c_539,plain,(
    ! [A_130,B_131] :
      ( ~ r2_hidden('#skF_4'(A_130,B_131,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_130,k10_relat_1('#skF_6',B_131))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_535,c_119])).

tff(c_543,plain,(
    ! [A_133,B_134] :
      ( ~ r2_hidden('#skF_4'(A_133,B_134,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_133,k10_relat_1('#skF_6',B_134)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_539])).

tff(c_547,plain,(
    ! [A_33] :
      ( ~ r2_hidden(A_33,k10_relat_1('#skF_6','#skF_5'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_543])).

tff(c_551,plain,(
    ! [A_135] : ~ r2_hidden(A_135,k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_547])).

tff(c_571,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_551])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_571])).

tff(c_580,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_32] :
      ( k9_relat_1(A_32,k1_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_588,plain,(
    ! [A_140,C_141,B_142] :
      ( ~ r2_hidden(A_140,C_141)
      | ~ r1_xboole_0(k2_tarski(A_140,B_142),C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_593,plain,(
    ! [A_140] : ~ r2_hidden(A_140,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_588])).

tff(c_581,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k4_tarski('#skF_3'(A_26,B_27,C_28),A_26),C_28)
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1245,plain,(
    ! [A_237,C_238,B_239,D_240] :
      ( r2_hidden(A_237,k10_relat_1(C_238,B_239))
      | ~ r2_hidden(D_240,B_239)
      | ~ r2_hidden(k4_tarski(A_237,D_240),C_238)
      | ~ r2_hidden(D_240,k2_relat_1(C_238))
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3072,plain,(
    ! [A_456,C_457,B_458,A_459] :
      ( r2_hidden(A_456,k10_relat_1(C_457,B_458))
      | ~ r2_hidden(k4_tarski(A_456,'#skF_1'(A_459,B_458)),C_457)
      | ~ r2_hidden('#skF_1'(A_459,B_458),k2_relat_1(C_457))
      | ~ v1_relat_1(C_457)
      | r1_xboole_0(A_459,B_458) ) ),
    inference(resolution,[status(thm)],[c_4,c_1245])).

tff(c_16340,plain,(
    ! [A_1204,B_1205,B_1206,C_1207] :
      ( r2_hidden('#skF_3'('#skF_1'(A_1204,B_1205),B_1206,C_1207),k10_relat_1(C_1207,B_1205))
      | ~ r2_hidden('#skF_1'(A_1204,B_1205),k2_relat_1(C_1207))
      | r1_xboole_0(A_1204,B_1205)
      | ~ r2_hidden('#skF_1'(A_1204,B_1205),k9_relat_1(C_1207,B_1206))
      | ~ v1_relat_1(C_1207) ) ),
    inference(resolution,[status(thm)],[c_26,c_3072])).

tff(c_16473,plain,(
    ! [A_1204,B_1206] :
      ( r2_hidden('#skF_3'('#skF_1'(A_1204,'#skF_5'),B_1206,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1204,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1204,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1204,'#skF_5'),k9_relat_1('#skF_6',B_1206))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_16340])).

tff(c_16516,plain,(
    ! [A_1204,B_1206] :
      ( r2_hidden('#skF_3'('#skF_1'(A_1204,'#skF_5'),B_1206,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1204,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1204,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1204,'#skF_5'),k9_relat_1('#skF_6',B_1206)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16473])).

tff(c_16518,plain,(
    ! [A_1208,B_1209] :
      ( ~ r2_hidden('#skF_1'(A_1208,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1208,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1208,'#skF_5'),k9_relat_1('#skF_6',B_1209)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_16516])).

tff(c_16592,plain,(
    ! [A_1208] :
      ( ~ r2_hidden('#skF_1'(A_1208,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1208,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1208,'#skF_5'),k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_16518])).

tff(c_16638,plain,(
    ! [A_1210] :
      ( r1_xboole_0(A_1210,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1210,'#skF_5'),k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16592])).

tff(c_16650,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_16638])).

tff(c_16661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_580,c_16650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.54/6.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.54/6.74  
% 13.54/6.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.54/6.74  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 13.54/6.74  
% 13.54/6.74  %Foreground sorts:
% 13.54/6.74  
% 13.54/6.74  
% 13.54/6.74  %Background operators:
% 13.54/6.74  
% 13.54/6.74  
% 13.54/6.74  %Foreground operators:
% 13.54/6.74  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.54/6.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.54/6.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.54/6.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.54/6.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.54/6.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.54/6.74  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.54/6.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.54/6.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.54/6.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.54/6.74  tff('#skF_5', type, '#skF_5': $i).
% 13.54/6.74  tff('#skF_6', type, '#skF_6': $i).
% 13.54/6.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.54/6.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.54/6.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.54/6.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.54/6.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.54/6.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.54/6.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.54/6.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.54/6.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.54/6.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.54/6.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.54/6.74  
% 13.63/6.76  tff(f_107, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 13.63/6.76  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.63/6.76  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 13.63/6.76  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.63/6.76  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 13.63/6.76  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 13.63/6.76  tff(f_66, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 13.63/6.76  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 13.63/6.76  tff(c_46, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5') | k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.63/6.76  tff(c_64, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 13.63/6.76  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.63/6.76  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.63/6.76  tff(c_34, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_4'(A_33, B_34, C_35), B_34) | ~r2_hidden(A_33, k10_relat_1(C_35, B_34)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.63/6.76  tff(c_535, plain, (![A_130, B_131, C_132]: (r2_hidden('#skF_4'(A_130, B_131, C_132), k2_relat_1(C_132)) | ~r2_hidden(A_130, k10_relat_1(C_132, B_131)) | ~v1_relat_1(C_132))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.63/6.76  tff(c_52, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.63/6.76  tff(c_87, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_52])).
% 13.63/6.76  tff(c_111, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, B_60) | ~r2_hidden(C_61, A_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.63/6.76  tff(c_119, plain, (![C_61]: (~r2_hidden(C_61, '#skF_5') | ~r2_hidden(C_61, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_87, c_111])).
% 13.63/6.76  tff(c_539, plain, (![A_130, B_131]: (~r2_hidden('#skF_4'(A_130, B_131, '#skF_6'), '#skF_5') | ~r2_hidden(A_130, k10_relat_1('#skF_6', B_131)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_535, c_119])).
% 13.63/6.76  tff(c_543, plain, (![A_133, B_134]: (~r2_hidden('#skF_4'(A_133, B_134, '#skF_6'), '#skF_5') | ~r2_hidden(A_133, k10_relat_1('#skF_6', B_134)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_539])).
% 13.63/6.76  tff(c_547, plain, (![A_33]: (~r2_hidden(A_33, k10_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_543])).
% 13.63/6.76  tff(c_551, plain, (![A_135]: (~r2_hidden(A_135, k10_relat_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_547])).
% 13.63/6.76  tff(c_571, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_551])).
% 13.63/6.76  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_571])).
% 13.63/6.76  tff(c_580, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 13.63/6.76  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.63/6.76  tff(c_30, plain, (![A_32]: (k9_relat_1(A_32, k1_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.63/6.76  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.63/6.76  tff(c_588, plain, (![A_140, C_141, B_142]: (~r2_hidden(A_140, C_141) | ~r1_xboole_0(k2_tarski(A_140, B_142), C_141))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.63/6.76  tff(c_593, plain, (![A_140]: (~r2_hidden(A_140, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_588])).
% 13.63/6.76  tff(c_581, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 13.63/6.76  tff(c_26, plain, (![A_26, B_27, C_28]: (r2_hidden(k4_tarski('#skF_3'(A_26, B_27, C_28), A_26), C_28) | ~r2_hidden(A_26, k9_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.63/6.76  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.63/6.76  tff(c_1245, plain, (![A_237, C_238, B_239, D_240]: (r2_hidden(A_237, k10_relat_1(C_238, B_239)) | ~r2_hidden(D_240, B_239) | ~r2_hidden(k4_tarski(A_237, D_240), C_238) | ~r2_hidden(D_240, k2_relat_1(C_238)) | ~v1_relat_1(C_238))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.63/6.76  tff(c_3072, plain, (![A_456, C_457, B_458, A_459]: (r2_hidden(A_456, k10_relat_1(C_457, B_458)) | ~r2_hidden(k4_tarski(A_456, '#skF_1'(A_459, B_458)), C_457) | ~r2_hidden('#skF_1'(A_459, B_458), k2_relat_1(C_457)) | ~v1_relat_1(C_457) | r1_xboole_0(A_459, B_458))), inference(resolution, [status(thm)], [c_4, c_1245])).
% 13.63/6.76  tff(c_16340, plain, (![A_1204, B_1205, B_1206, C_1207]: (r2_hidden('#skF_3'('#skF_1'(A_1204, B_1205), B_1206, C_1207), k10_relat_1(C_1207, B_1205)) | ~r2_hidden('#skF_1'(A_1204, B_1205), k2_relat_1(C_1207)) | r1_xboole_0(A_1204, B_1205) | ~r2_hidden('#skF_1'(A_1204, B_1205), k9_relat_1(C_1207, B_1206)) | ~v1_relat_1(C_1207))), inference(resolution, [status(thm)], [c_26, c_3072])).
% 13.63/6.76  tff(c_16473, plain, (![A_1204, B_1206]: (r2_hidden('#skF_3'('#skF_1'(A_1204, '#skF_5'), B_1206, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1204, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1204, '#skF_5') | ~r2_hidden('#skF_1'(A_1204, '#skF_5'), k9_relat_1('#skF_6', B_1206)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_581, c_16340])).
% 13.63/6.76  tff(c_16516, plain, (![A_1204, B_1206]: (r2_hidden('#skF_3'('#skF_1'(A_1204, '#skF_5'), B_1206, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1204, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1204, '#skF_5') | ~r2_hidden('#skF_1'(A_1204, '#skF_5'), k9_relat_1('#skF_6', B_1206)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16473])).
% 13.63/6.76  tff(c_16518, plain, (![A_1208, B_1209]: (~r2_hidden('#skF_1'(A_1208, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1208, '#skF_5') | ~r2_hidden('#skF_1'(A_1208, '#skF_5'), k9_relat_1('#skF_6', B_1209)))), inference(negUnitSimplification, [status(thm)], [c_593, c_16516])).
% 13.63/6.76  tff(c_16592, plain, (![A_1208]: (~r2_hidden('#skF_1'(A_1208, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1208, '#skF_5') | ~r2_hidden('#skF_1'(A_1208, '#skF_5'), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_16518])).
% 13.63/6.76  tff(c_16638, plain, (![A_1210]: (r1_xboole_0(A_1210, '#skF_5') | ~r2_hidden('#skF_1'(A_1210, '#skF_5'), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16592])).
% 13.63/6.76  tff(c_16650, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_16638])).
% 13.63/6.76  tff(c_16661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_580, c_580, c_16650])).
% 13.63/6.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.63/6.76  
% 13.63/6.76  Inference rules
% 13.63/6.76  ----------------------
% 13.63/6.76  #Ref     : 0
% 13.63/6.76  #Sup     : 3850
% 13.63/6.76  #Fact    : 0
% 13.63/6.76  #Define  : 0
% 13.63/6.76  #Split   : 20
% 13.63/6.76  #Chain   : 0
% 13.63/6.76  #Close   : 0
% 13.63/6.76  
% 13.63/6.76  Ordering : KBO
% 13.63/6.76  
% 13.63/6.76  Simplification rules
% 13.63/6.76  ----------------------
% 13.63/6.76  #Subsume      : 2121
% 13.63/6.76  #Demod        : 1077
% 13.63/6.76  #Tautology    : 788
% 13.63/6.76  #SimpNegUnit  : 71
% 13.63/6.76  #BackRed      : 0
% 13.63/6.76  
% 13.63/6.76  #Partial instantiations: 0
% 13.63/6.76  #Strategies tried      : 1
% 13.63/6.76  
% 13.63/6.76  Timing (in seconds)
% 13.63/6.76  ----------------------
% 13.63/6.76  Preprocessing        : 0.30
% 13.63/6.76  Parsing              : 0.16
% 13.63/6.76  CNF conversion       : 0.02
% 13.63/6.76  Main loop            : 5.66
% 13.63/6.76  Inferencing          : 0.86
% 13.63/6.76  Reduction            : 0.55
% 13.63/6.76  Demodulation         : 0.36
% 13.63/6.76  BG Simplification    : 0.06
% 13.63/6.76  Subsumption          : 4.06
% 13.63/6.76  Abstraction          : 0.09
% 13.63/6.76  MUC search           : 0.00
% 13.63/6.76  Cooper               : 0.00
% 13.63/6.76  Total                : 5.99
% 13.63/6.76  Index Insertion      : 0.00
% 13.63/6.76  Index Deletion       : 0.00
% 13.63/6.76  Index Matching       : 0.00
% 13.63/6.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
