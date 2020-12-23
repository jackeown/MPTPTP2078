%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:28 EST 2020

% Result     : Theorem 10.18s
% Output     : CNFRefutation 10.18s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 212 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  140 ( 543 expanded)
%              Number of equality atoms :   32 ( 105 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_76,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8')
    | k9_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_67,plain,(
    k9_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_7'(A_34,B_35),A_34)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden('#skF_6'(A_26,B_27,C_28),B_27)
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_431,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_6'(A_109,B_110,C_111),k1_relat_1(C_111))
      | ~ r2_hidden(A_109,k9_relat_1(C_111,B_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,
    ( k9_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_68,plain,(
    r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_48])).

tff(c_85,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_90,plain,(
    ! [C_58] :
      ( ~ r2_hidden(C_58,'#skF_8')
      | ~ r2_hidden(C_58,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_68,c_85])).

tff(c_445,plain,(
    ! [A_109,B_110] :
      ( ~ r2_hidden('#skF_6'(A_109,B_110,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_109,k9_relat_1('#skF_9',B_110))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_431,c_90])).

tff(c_477,plain,(
    ! [A_115,B_116] :
      ( ~ r2_hidden('#skF_6'(A_115,B_116,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_115,k9_relat_1('#skF_9',B_116)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_445])).

tff(c_481,plain,(
    ! [A_26] :
      ( ~ r2_hidden(A_26,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_477])).

tff(c_489,plain,(
    ! [A_117] : ~ r2_hidden(A_117,k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_481])).

tff(c_525,plain,(
    ! [B_119] : r1_xboole_0(k9_relat_1('#skF_9','#skF_8'),B_119) ),
    inference(resolution,[status(thm)],[c_36,c_489])).

tff(c_14,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_577,plain,(
    ! [B_122] : k3_xboole_0(k9_relat_1('#skF_9','#skF_8'),B_122) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_525,c_14])).

tff(c_20,plain,(
    ! [A_24] : k3_xboole_0(A_24,A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_591,plain,(
    k9_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_20])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_591])).

tff(c_610,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_7'(A_34,B_35),B_35)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_827,plain,(
    ! [A_168,B_169,C_170] :
      ( r2_hidden('#skF_6'(A_168,B_169,C_170),k1_relat_1(C_170))
      | ~ r2_hidden(A_168,k9_relat_1(C_170,B_169))
      | ~ v1_relat_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_624,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ r1_xboole_0(A_127,B_128)
      | ~ r2_hidden(C_129,B_128)
      | ~ r2_hidden(C_129,A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_634,plain,(
    ! [C_133,B_134,A_135] :
      ( ~ r2_hidden(C_133,B_134)
      | ~ r2_hidden(C_133,A_135)
      | k3_xboole_0(A_135,B_134) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_624])).

tff(c_666,plain,(
    ! [A_144,B_145,A_146] :
      ( ~ r2_hidden('#skF_7'(A_144,B_145),A_146)
      | k3_xboole_0(A_146,A_144) != k1_xboole_0
      | r1_xboole_0(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_36,c_634])).

tff(c_673,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,A_34) != k1_xboole_0
      | r1_xboole_0(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_36,c_666])).

tff(c_682,plain,(
    ! [A_147,B_148] :
      ( k1_xboole_0 != A_147
      | r1_xboole_0(A_147,B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_673])).

tff(c_32,plain,(
    ! [A_34,B_35,C_38] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_38,B_35)
      | ~ r2_hidden(C_38,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_691,plain,(
    ! [C_38,B_148,A_147] :
      ( ~ r2_hidden(C_38,B_148)
      | ~ r2_hidden(C_38,A_147)
      | k1_xboole_0 != A_147 ) ),
    inference(resolution,[status(thm)],[c_682,c_32])).

tff(c_1194,plain,(
    ! [A_238,B_239,C_240,A_241] :
      ( ~ r2_hidden('#skF_6'(A_238,B_239,C_240),A_241)
      | k1_xboole_0 != A_241
      | ~ r2_hidden(A_238,k9_relat_1(C_240,B_239))
      | ~ v1_relat_1(C_240) ) ),
    inference(resolution,[status(thm)],[c_827,c_691])).

tff(c_1218,plain,(
    ! [B_245,A_246,C_247] :
      ( k1_xboole_0 != B_245
      | ~ r2_hidden(A_246,k9_relat_1(C_247,B_245))
      | ~ v1_relat_1(C_247) ) ),
    inference(resolution,[status(thm)],[c_24,c_1194])).

tff(c_1284,plain,(
    ! [B_251,C_252,A_253] :
      ( k1_xboole_0 != B_251
      | ~ v1_relat_1(C_252)
      | r1_xboole_0(A_253,k9_relat_1(C_252,B_251)) ) ),
    inference(resolution,[status(thm)],[c_34,c_1218])).

tff(c_1437,plain,(
    ! [A_266,C_267,B_268] :
      ( k3_xboole_0(A_266,k9_relat_1(C_267,B_268)) = k1_xboole_0
      | k1_xboole_0 != B_268
      | ~ v1_relat_1(C_267) ) ),
    inference(resolution,[status(thm)],[c_1284,c_14])).

tff(c_1483,plain,(
    ! [C_269,B_270] :
      ( k9_relat_1(C_269,B_270) = k1_xboole_0
      | k1_xboole_0 != B_270
      | ~ v1_relat_1(C_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1437,c_20])).

tff(c_1532,plain,(
    ! [B_273] :
      ( k9_relat_1('#skF_9',B_273) = k1_xboole_0
      | k1_xboole_0 != B_273 ) ),
    inference(resolution,[status(thm)],[c_40,c_1483])).

tff(c_1206,plain,(
    ! [B_27,A_26,C_28] :
      ( k1_xboole_0 != B_27
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(resolution,[status(thm)],[c_24,c_1194])).

tff(c_1559,plain,(
    ! [B_273,A_26] :
      ( k1_xboole_0 != B_273
      | ~ r2_hidden(A_26,k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | k1_xboole_0 != B_273 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1532,c_1206])).

tff(c_1585,plain,(
    ! [A_26,B_273] :
      ( ~ r2_hidden(A_26,k1_xboole_0)
      | k1_xboole_0 != B_273 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1559])).

tff(c_1587,plain,(
    ! [B_273] : k1_xboole_0 != B_273 ),
    inference(splitLeft,[status(thm)],[c_1585])).

tff(c_611,plain,(
    k9_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_611])).

tff(c_1598,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1585])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1145,plain,(
    ! [A_225,C_226,B_227,D_228] :
      ( r2_hidden(A_225,k9_relat_1(C_226,B_227))
      | ~ r2_hidden(D_228,B_227)
      | ~ r2_hidden(k4_tarski(D_228,A_225),C_226)
      | ~ r2_hidden(D_228,k1_relat_1(C_226))
      | ~ v1_relat_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2226,plain,(
    ! [A_304,C_305,B_306,A_307] :
      ( r2_hidden(A_304,k9_relat_1(C_305,B_306))
      | ~ r2_hidden(k4_tarski('#skF_7'(A_307,B_306),A_304),C_305)
      | ~ r2_hidden('#skF_7'(A_307,B_306),k1_relat_1(C_305))
      | ~ v1_relat_1(C_305)
      | r1_xboole_0(A_307,B_306) ) ),
    inference(resolution,[status(thm)],[c_34,c_1145])).

tff(c_24278,plain,(
    ! [A_679,A_680,B_681] :
      ( r2_hidden('#skF_4'(A_679,k1_relat_1(A_679),'#skF_7'(A_680,B_681)),k9_relat_1(A_679,B_681))
      | ~ v1_relat_1(A_679)
      | r1_xboole_0(A_680,B_681)
      | ~ r2_hidden('#skF_7'(A_680,B_681),k1_relat_1(A_679)) ) ),
    inference(resolution,[status(thm)],[c_2,c_2226])).

tff(c_24443,plain,(
    ! [A_680] :
      ( r2_hidden('#skF_4'('#skF_9',k1_relat_1('#skF_9'),'#skF_7'(A_680,'#skF_8')),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | r1_xboole_0(A_680,'#skF_8')
      | ~ r2_hidden('#skF_7'(A_680,'#skF_8'),k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_24278])).

tff(c_24473,plain,(
    ! [A_680] :
      ( r2_hidden('#skF_4'('#skF_9',k1_relat_1('#skF_9'),'#skF_7'(A_680,'#skF_8')),k1_xboole_0)
      | r1_xboole_0(A_680,'#skF_8')
      | ~ r2_hidden('#skF_7'(A_680,'#skF_8'),k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24443])).

tff(c_24475,plain,(
    ! [A_682] :
      ( r1_xboole_0(A_682,'#skF_8')
      | ~ r2_hidden('#skF_7'(A_682,'#skF_8'),k1_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1598,c_24473])).

tff(c_24491,plain,(
    r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_24475])).

tff(c_24496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_610,c_24491])).

%------------------------------------------------------------------------------
