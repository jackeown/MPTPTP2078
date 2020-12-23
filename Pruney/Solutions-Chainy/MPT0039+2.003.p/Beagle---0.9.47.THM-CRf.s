%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:42 EST 2020

% Result     : Theorem 14.39s
% Output     : CNFRefutation 14.39s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 628 expanded)
%              Number of leaves         :   14 ( 218 expanded)
%              Depth                    :   15
%              Number of atoms          :  160 (1609 expanded)
%              Number of equality atoms :   39 ( 459 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    ! [D_12,A_13,B_14] :
      ( r2_hidden(D_12,A_13)
      | ~ r2_hidden(D_12,k4_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,'#skF_5')
      | ~ r2_hidden(D_23,k4_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_33])).

tff(c_71,plain,(
    ! [B_25] :
      ( r2_hidden('#skF_1'(k4_xboole_0('#skF_4','#skF_5'),B_25),'#skF_5')
      | r1_tarski(k4_xboole_0('#skF_4','#skF_5'),B_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    r1_tarski(k4_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_77,plain,(
    ! [C_26,B_27,A_28] :
      ( r2_hidden(C_26,B_27)
      | ~ r2_hidden(C_26,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_207,plain,(
    ! [A_42,B_43,B_44] :
      ( r2_hidden('#skF_1'(A_42,B_43),B_44)
      | ~ r1_tarski(A_42,B_44)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_84,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,k4_xboole_0(A_30,B_31))
      | r2_hidden(D_29,B_31)
      | ~ r2_hidden(D_29,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_145,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,k4_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(D_39,'#skF_4')
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_84])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_173,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,'#skF_4')
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_241,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),'#skF_4')
      | ~ r1_tarski(A_42,'#skF_5')
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_207,c_173])).

tff(c_37,plain,(
    ! [D_15,B_16,A_17] :
      ( ~ r2_hidden(D_15,B_16)
      | ~ r2_hidden(D_15,k4_xboole_0(A_17,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [D_24] :
      ( ~ r2_hidden(D_24,'#skF_4')
      | ~ r2_hidden(D_24,k4_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_37])).

tff(c_297,plain,(
    ! [B_52] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0('#skF_4','#skF_5'),B_52),'#skF_4')
      | r1_tarski(k4_xboole_0('#skF_4','#skF_5'),B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_301,plain,(
    ! [B_43] :
      ( ~ r1_tarski(k4_xboole_0('#skF_4','#skF_5'),'#skF_5')
      | r1_tarski(k4_xboole_0('#skF_4','#skF_5'),B_43) ) ),
    inference(resolution,[status(thm)],[c_241,c_297])).

tff(c_308,plain,(
    ! [B_43] : r1_tarski(k4_xboole_0('#skF_4','#skF_5'),B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_301])).

tff(c_372,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden('#skF_2'(A_56,B_57,C_58),A_56)
      | r2_hidden('#skF_3'(A_56,B_57,C_58),C_58)
      | k4_xboole_0(A_56,B_57) = C_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_459,plain,(
    ! [A_60,C_61] :
      ( r2_hidden('#skF_3'(A_60,A_60,C_61),C_61)
      | k4_xboole_0(A_60,A_60) = C_61 ) ),
    inference(resolution,[status(thm)],[c_372,c_22])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_487,plain,(
    ! [A_60,C_61,B_2] :
      ( r2_hidden('#skF_3'(A_60,A_60,C_61),B_2)
      | ~ r1_tarski(C_61,B_2)
      | k4_xboole_0(A_60,A_60) = C_61 ) ),
    inference(resolution,[status(thm)],[c_459,c_2])).

tff(c_40,plain,(
    ! [D_15] :
      ( ~ r2_hidden(D_15,'#skF_4')
      | ~ r2_hidden(D_15,k4_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_37])).

tff(c_1697,plain,(
    ! [A_163] :
      ( ~ r2_hidden('#skF_3'(A_163,A_163,k4_xboole_0('#skF_4','#skF_5')),'#skF_4')
      | k4_xboole_0(A_163,A_163) = k4_xboole_0('#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_459,c_40])).

tff(c_1701,plain,(
    ! [A_60] :
      ( ~ r1_tarski(k4_xboole_0('#skF_4','#skF_5'),'#skF_4')
      | k4_xboole_0(A_60,A_60) = k4_xboole_0('#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_487,c_1697])).

tff(c_1710,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_1701])).

tff(c_26,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_492,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63,A_62),A_62)
      | k4_xboole_0(A_62,B_63) = A_62 ) ),
    inference(resolution,[status(thm)],[c_372,c_20])).

tff(c_518,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_3'('#skF_5',B_63,'#skF_5'),'#skF_4')
      | k4_xboole_0('#skF_5',B_63) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_492,c_173])).

tff(c_429,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_3'(A_56,B_57,A_56),A_56)
      | k4_xboole_0(A_56,B_57) = A_56 ) ),
    inference(resolution,[status(thm)],[c_372,c_20])).

tff(c_959,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_2'(A_103,B_104,C_105),A_103)
      | r2_hidden('#skF_3'(A_103,B_104,C_105),B_104)
      | ~ r2_hidden('#skF_3'(A_103,B_104,C_105),A_103)
      | k4_xboole_0(A_103,B_104) = C_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1451,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_3'(A_142,B_143,A_142),B_143)
      | ~ r2_hidden('#skF_3'(A_142,B_143,A_142),A_142)
      | k4_xboole_0(A_142,B_143) = A_142 ) ),
    inference(resolution,[status(thm)],[c_959,c_14])).

tff(c_1495,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_3'(A_147,B_148,A_147),B_148)
      | k4_xboole_0(A_147,B_148) = A_147 ) ),
    inference(resolution,[status(thm)],[c_429,c_1451])).

tff(c_3824,plain,(
    ! [A_224] :
      ( ~ r2_hidden('#skF_3'(A_224,k4_xboole_0('#skF_4','#skF_5'),A_224),'#skF_4')
      | k4_xboole_0(A_224,k4_xboole_0('#skF_4','#skF_5')) = A_224 ) ),
    inference(resolution,[status(thm)],[c_1495,c_40])).

tff(c_3854,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_518,c_3824])).

tff(c_175,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_4')
      | ~ r2_hidden(D_40,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_189,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_1'('#skF_5',B_41),'#skF_4')
      | r1_tarski('#skF_5',B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_206,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_4])).

tff(c_1574,plain,(
    ! [A_154,B_155,C_156,B_157] :
      ( r2_hidden('#skF_2'(A_154,B_155,C_156),B_157)
      | ~ r1_tarski(A_154,B_157)
      | r2_hidden('#skF_3'(A_154,B_155,C_156),C_156)
      | k4_xboole_0(A_154,B_155) = C_156 ) ),
    inference(resolution,[status(thm)],[c_372,c_2])).

tff(c_1639,plain,(
    ! [A_154,B_157,B_155] :
      ( ~ r1_tarski(A_154,B_157)
      | r2_hidden('#skF_3'(A_154,B_155,B_157),B_157)
      | k4_xboole_0(A_154,B_155) = B_157 ) ),
    inference(resolution,[status(thm)],[c_1574,c_20])).

tff(c_109,plain,(
    ! [D_29] :
      ( r2_hidden(D_29,'#skF_5')
      | ~ r2_hidden(D_29,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_84,c_40])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6104,plain,(
    ! [A_278,A_279,B_280,C_281] :
      ( ~ r2_hidden('#skF_3'(A_278,k4_xboole_0(A_279,B_280),C_281),B_280)
      | r2_hidden('#skF_2'(A_278,k4_xboole_0(A_279,B_280),C_281),A_278)
      | ~ r2_hidden('#skF_3'(A_278,k4_xboole_0(A_279,B_280),C_281),A_278)
      | k4_xboole_0(A_278,k4_xboole_0(A_279,B_280)) = C_281 ) ),
    inference(resolution,[status(thm)],[c_959,c_10])).

tff(c_32823,plain,(
    ! [A_610,A_611,C_612] :
      ( ~ r2_hidden('#skF_3'(A_610,k4_xboole_0(A_611,C_612),C_612),A_610)
      | r2_hidden('#skF_2'(A_610,k4_xboole_0(A_611,C_612),C_612),A_610)
      | k4_xboole_0(A_610,k4_xboole_0(A_611,C_612)) = C_612 ) ),
    inference(resolution,[status(thm)],[c_24,c_6104])).

tff(c_32987,plain,(
    ! [A_610] :
      ( ~ r2_hidden('#skF_3'(A_610,k4_xboole_0('#skF_5','#skF_4'),'#skF_4'),A_610)
      | r2_hidden('#skF_2'(A_610,k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),A_610)
      | k4_xboole_0(A_610,k4_xboole_0('#skF_5','#skF_4')) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_32823])).

tff(c_33352,plain,(
    ! [A_616] :
      ( ~ r2_hidden('#skF_3'(A_616,k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),A_616)
      | r2_hidden('#skF_2'(A_616,k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),A_616)
      | k4_xboole_0(A_616,k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_32987])).

tff(c_33427,plain,
    ( r2_hidden('#skF_2'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_5')
    | k4_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_33352,c_173])).

tff(c_33490,plain,
    ( r2_hidden('#skF_2'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3854,c_33427])).

tff(c_33491,plain,
    ( r2_hidden('#skF_2'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_33490])).

tff(c_34222,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_33491])).

tff(c_34229,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_34222])).

tff(c_34298,plain,
    ( ~ r1_tarski('#skF_5','#skF_4')
    | k4_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1639,c_34229])).

tff(c_34311,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3854,c_206,c_34298])).

tff(c_34313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_34311])).

tff(c_34315,plain,(
    r2_hidden('#skF_3'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_33491])).

tff(c_34372,plain,(
    ! [A_60] : r2_hidden('#skF_3'('#skF_5',k4_xboole_0(A_60,A_60),'#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1710,c_34315])).

tff(c_3902,plain,(
    ! [A_60] : k4_xboole_0('#skF_5',k4_xboole_0(A_60,A_60)) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1710,c_3854])).

tff(c_34314,plain,(
    r2_hidden('#skF_2'('#skF_5',k4_xboole_0('#skF_4','#skF_5'),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_33491])).

tff(c_34964,plain,(
    ! [A_634] : r2_hidden('#skF_2'('#skF_5',k4_xboole_0(A_634,A_634),'#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1710,c_34314])).

tff(c_34977,plain,(
    ! [A_634] :
      ( r2_hidden('#skF_3'('#skF_5',k4_xboole_0(A_634,A_634),'#skF_4'),k4_xboole_0(A_634,A_634))
      | ~ r2_hidden('#skF_3'('#skF_5',k4_xboole_0(A_634,A_634),'#skF_4'),'#skF_5')
      | k4_xboole_0('#skF_5',k4_xboole_0(A_634,A_634)) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_34964,c_14])).

tff(c_35048,plain,(
    ! [A_634] :
      ( r2_hidden('#skF_3'('#skF_5',k4_xboole_0(A_634,A_634),'#skF_4'),k4_xboole_0(A_634,A_634))
      | '#skF_5' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3902,c_34372,c_34977])).

tff(c_35496,plain,(
    ! [A_640] : r2_hidden('#skF_3'('#skF_5',k4_xboole_0(A_640,A_640),'#skF_4'),k4_xboole_0(A_640,A_640)) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_35048])).

tff(c_1521,plain,(
    ! [A_147] :
      ( r2_hidden('#skF_3'(A_147,'#skF_5',A_147),'#skF_4')
      | k4_xboole_0(A_147,'#skF_5') = A_147 ) ),
    inference(resolution,[status(thm)],[c_1495,c_173])).

tff(c_20680,plain,(
    ! [A_505,B_506,B_507] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_505,B_506),B_507,k4_xboole_0(A_505,B_506)),B_506)
      | k4_xboole_0(k4_xboole_0(A_505,B_506),B_507) = k4_xboole_0(A_505,B_506) ) ),
    inference(resolution,[status(thm)],[c_492,c_10])).

tff(c_22128,plain,(
    ! [A_512] : k4_xboole_0(k4_xboole_0(A_512,'#skF_4'),'#skF_5') = k4_xboole_0(A_512,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1521,c_20680])).

tff(c_22346,plain,(
    ! [D_11,A_512] :
      ( ~ r2_hidden(D_11,'#skF_5')
      | ~ r2_hidden(D_11,k4_xboole_0(A_512,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22128,c_10])).

tff(c_35508,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k4_xboole_0('#skF_4','#skF_4'),'#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_35496,c_22346])).

tff(c_35658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34372,c_35508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:13:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.39/6.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.39/6.06  
% 14.39/6.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.39/6.06  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 14.39/6.06  
% 14.39/6.06  %Foreground sorts:
% 14.39/6.06  
% 14.39/6.06  
% 14.39/6.06  %Background operators:
% 14.39/6.06  
% 14.39/6.06  
% 14.39/6.06  %Foreground operators:
% 14.39/6.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.39/6.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.39/6.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.39/6.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.39/6.06  tff('#skF_5', type, '#skF_5': $i).
% 14.39/6.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.39/6.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.39/6.06  tff('#skF_4', type, '#skF_4': $i).
% 14.39/6.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.39/6.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.39/6.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.39/6.07  
% 14.39/6.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.39/6.08  tff(f_47, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 14.39/6.08  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.39/6.08  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.39/6.08  tff(c_28, plain, (k4_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.39/6.08  tff(c_33, plain, (![D_12, A_13, B_14]: (r2_hidden(D_12, A_13) | ~r2_hidden(D_12, k4_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_59, plain, (![D_23]: (r2_hidden(D_23, '#skF_5') | ~r2_hidden(D_23, k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_33])).
% 14.39/6.08  tff(c_71, plain, (![B_25]: (r2_hidden('#skF_1'(k4_xboole_0('#skF_4', '#skF_5'), B_25), '#skF_5') | r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), B_25))), inference(resolution, [status(thm)], [c_6, c_59])).
% 14.39/6.08  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.39/6.08  tff(c_76, plain, (r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_71, c_4])).
% 14.39/6.08  tff(c_77, plain, (![C_26, B_27, A_28]: (r2_hidden(C_26, B_27) | ~r2_hidden(C_26, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.39/6.08  tff(c_207, plain, (![A_42, B_43, B_44]: (r2_hidden('#skF_1'(A_42, B_43), B_44) | ~r1_tarski(A_42, B_44) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_77])).
% 14.39/6.08  tff(c_84, plain, (![D_29, A_30, B_31]: (r2_hidden(D_29, k4_xboole_0(A_30, B_31)) | r2_hidden(D_29, B_31) | ~r2_hidden(D_29, A_30))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_145, plain, (![D_39]: (r2_hidden(D_39, k4_xboole_0('#skF_4', '#skF_5')) | r2_hidden(D_39, '#skF_4') | ~r2_hidden(D_39, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_84])).
% 14.39/6.08  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_173, plain, (![D_39]: (r2_hidden(D_39, '#skF_4') | ~r2_hidden(D_39, '#skF_5'))), inference(resolution, [status(thm)], [c_145, c_10])).
% 14.39/6.08  tff(c_241, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), '#skF_4') | ~r1_tarski(A_42, '#skF_5') | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_207, c_173])).
% 14.39/6.08  tff(c_37, plain, (![D_15, B_16, A_17]: (~r2_hidden(D_15, B_16) | ~r2_hidden(D_15, k4_xboole_0(A_17, B_16)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_65, plain, (![D_24]: (~r2_hidden(D_24, '#skF_4') | ~r2_hidden(D_24, k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_37])).
% 14.39/6.08  tff(c_297, plain, (![B_52]: (~r2_hidden('#skF_1'(k4_xboole_0('#skF_4', '#skF_5'), B_52), '#skF_4') | r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), B_52))), inference(resolution, [status(thm)], [c_6, c_65])).
% 14.39/6.08  tff(c_301, plain, (![B_43]: (~r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), '#skF_5') | r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), B_43))), inference(resolution, [status(thm)], [c_241, c_297])).
% 14.39/6.08  tff(c_308, plain, (![B_43]: (r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), B_43))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_301])).
% 14.39/6.08  tff(c_372, plain, (![A_56, B_57, C_58]: (r2_hidden('#skF_2'(A_56, B_57, C_58), A_56) | r2_hidden('#skF_3'(A_56, B_57, C_58), C_58) | k4_xboole_0(A_56, B_57)=C_58)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_459, plain, (![A_60, C_61]: (r2_hidden('#skF_3'(A_60, A_60, C_61), C_61) | k4_xboole_0(A_60, A_60)=C_61)), inference(resolution, [status(thm)], [c_372, c_22])).
% 14.39/6.08  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.39/6.08  tff(c_487, plain, (![A_60, C_61, B_2]: (r2_hidden('#skF_3'(A_60, A_60, C_61), B_2) | ~r1_tarski(C_61, B_2) | k4_xboole_0(A_60, A_60)=C_61)), inference(resolution, [status(thm)], [c_459, c_2])).
% 14.39/6.08  tff(c_40, plain, (![D_15]: (~r2_hidden(D_15, '#skF_4') | ~r2_hidden(D_15, k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_37])).
% 14.39/6.08  tff(c_1697, plain, (![A_163]: (~r2_hidden('#skF_3'(A_163, A_163, k4_xboole_0('#skF_4', '#skF_5')), '#skF_4') | k4_xboole_0(A_163, A_163)=k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_459, c_40])).
% 14.39/6.08  tff(c_1701, plain, (![A_60]: (~r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4') | k4_xboole_0(A_60, A_60)=k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_487, c_1697])).
% 14.39/6.08  tff(c_1710, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k4_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_1701])).
% 14.39/6.08  tff(c_26, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.39/6.08  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_492, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63, A_62), A_62) | k4_xboole_0(A_62, B_63)=A_62)), inference(resolution, [status(thm)], [c_372, c_20])).
% 14.39/6.08  tff(c_518, plain, (![B_63]: (r2_hidden('#skF_3'('#skF_5', B_63, '#skF_5'), '#skF_4') | k4_xboole_0('#skF_5', B_63)='#skF_5')), inference(resolution, [status(thm)], [c_492, c_173])).
% 14.39/6.08  tff(c_429, plain, (![A_56, B_57]: (r2_hidden('#skF_3'(A_56, B_57, A_56), A_56) | k4_xboole_0(A_56, B_57)=A_56)), inference(resolution, [status(thm)], [c_372, c_20])).
% 14.39/6.08  tff(c_959, plain, (![A_103, B_104, C_105]: (r2_hidden('#skF_2'(A_103, B_104, C_105), A_103) | r2_hidden('#skF_3'(A_103, B_104, C_105), B_104) | ~r2_hidden('#skF_3'(A_103, B_104, C_105), A_103) | k4_xboole_0(A_103, B_104)=C_105)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_14, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_1451, plain, (![A_142, B_143]: (r2_hidden('#skF_3'(A_142, B_143, A_142), B_143) | ~r2_hidden('#skF_3'(A_142, B_143, A_142), A_142) | k4_xboole_0(A_142, B_143)=A_142)), inference(resolution, [status(thm)], [c_959, c_14])).
% 14.39/6.08  tff(c_1495, plain, (![A_147, B_148]: (r2_hidden('#skF_3'(A_147, B_148, A_147), B_148) | k4_xboole_0(A_147, B_148)=A_147)), inference(resolution, [status(thm)], [c_429, c_1451])).
% 14.39/6.08  tff(c_3824, plain, (![A_224]: (~r2_hidden('#skF_3'(A_224, k4_xboole_0('#skF_4', '#skF_5'), A_224), '#skF_4') | k4_xboole_0(A_224, k4_xboole_0('#skF_4', '#skF_5'))=A_224)), inference(resolution, [status(thm)], [c_1495, c_40])).
% 14.39/6.08  tff(c_3854, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_518, c_3824])).
% 14.39/6.08  tff(c_175, plain, (![D_40]: (r2_hidden(D_40, '#skF_4') | ~r2_hidden(D_40, '#skF_5'))), inference(resolution, [status(thm)], [c_145, c_10])).
% 14.39/6.08  tff(c_189, plain, (![B_41]: (r2_hidden('#skF_1'('#skF_5', B_41), '#skF_4') | r1_tarski('#skF_5', B_41))), inference(resolution, [status(thm)], [c_6, c_175])).
% 14.39/6.08  tff(c_206, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_189, c_4])).
% 14.39/6.08  tff(c_1574, plain, (![A_154, B_155, C_156, B_157]: (r2_hidden('#skF_2'(A_154, B_155, C_156), B_157) | ~r1_tarski(A_154, B_157) | r2_hidden('#skF_3'(A_154, B_155, C_156), C_156) | k4_xboole_0(A_154, B_155)=C_156)), inference(resolution, [status(thm)], [c_372, c_2])).
% 14.39/6.08  tff(c_1639, plain, (![A_154, B_157, B_155]: (~r1_tarski(A_154, B_157) | r2_hidden('#skF_3'(A_154, B_155, B_157), B_157) | k4_xboole_0(A_154, B_155)=B_157)), inference(resolution, [status(thm)], [c_1574, c_20])).
% 14.39/6.08  tff(c_109, plain, (![D_29]: (r2_hidden(D_29, '#skF_5') | ~r2_hidden(D_29, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_40])).
% 14.39/6.08  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.39/6.08  tff(c_6104, plain, (![A_278, A_279, B_280, C_281]: (~r2_hidden('#skF_3'(A_278, k4_xboole_0(A_279, B_280), C_281), B_280) | r2_hidden('#skF_2'(A_278, k4_xboole_0(A_279, B_280), C_281), A_278) | ~r2_hidden('#skF_3'(A_278, k4_xboole_0(A_279, B_280), C_281), A_278) | k4_xboole_0(A_278, k4_xboole_0(A_279, B_280))=C_281)), inference(resolution, [status(thm)], [c_959, c_10])).
% 14.39/6.08  tff(c_32823, plain, (![A_610, A_611, C_612]: (~r2_hidden('#skF_3'(A_610, k4_xboole_0(A_611, C_612), C_612), A_610) | r2_hidden('#skF_2'(A_610, k4_xboole_0(A_611, C_612), C_612), A_610) | k4_xboole_0(A_610, k4_xboole_0(A_611, C_612))=C_612)), inference(resolution, [status(thm)], [c_24, c_6104])).
% 14.39/6.08  tff(c_32987, plain, (![A_610]: (~r2_hidden('#skF_3'(A_610, k4_xboole_0('#skF_5', '#skF_4'), '#skF_4'), A_610) | r2_hidden('#skF_2'(A_610, k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), A_610) | k4_xboole_0(A_610, k4_xboole_0('#skF_5', '#skF_4'))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_32823])).
% 14.39/6.08  tff(c_33352, plain, (![A_616]: (~r2_hidden('#skF_3'(A_616, k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), A_616) | r2_hidden('#skF_2'(A_616, k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), A_616) | k4_xboole_0(A_616, k4_xboole_0('#skF_4', '#skF_5'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_32987])).
% 14.39/6.08  tff(c_33427, plain, (r2_hidden('#skF_2'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_5') | k4_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_33352, c_173])).
% 14.39/6.08  tff(c_33490, plain, (r2_hidden('#skF_2'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3854, c_33427])).
% 14.39/6.08  tff(c_33491, plain, (r2_hidden('#skF_2'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_26, c_33490])).
% 14.39/6.08  tff(c_34222, plain, (~r2_hidden('#skF_3'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_33491])).
% 14.39/6.08  tff(c_34229, plain, (~r2_hidden('#skF_3'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_109, c_34222])).
% 14.39/6.08  tff(c_34298, plain, (~r1_tarski('#skF_5', '#skF_4') | k4_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_1639, c_34229])).
% 14.39/6.08  tff(c_34311, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3854, c_206, c_34298])).
% 14.39/6.08  tff(c_34313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_34311])).
% 14.39/6.08  tff(c_34315, plain, (r2_hidden('#skF_3'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_33491])).
% 14.39/6.08  tff(c_34372, plain, (![A_60]: (r2_hidden('#skF_3'('#skF_5', k4_xboole_0(A_60, A_60), '#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1710, c_34315])).
% 14.39/6.08  tff(c_3902, plain, (![A_60]: (k4_xboole_0('#skF_5', k4_xboole_0(A_60, A_60))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1710, c_3854])).
% 14.39/6.08  tff(c_34314, plain, (r2_hidden('#skF_2'('#skF_5', k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_33491])).
% 14.39/6.08  tff(c_34964, plain, (![A_634]: (r2_hidden('#skF_2'('#skF_5', k4_xboole_0(A_634, A_634), '#skF_4'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1710, c_34314])).
% 14.39/6.08  tff(c_34977, plain, (![A_634]: (r2_hidden('#skF_3'('#skF_5', k4_xboole_0(A_634, A_634), '#skF_4'), k4_xboole_0(A_634, A_634)) | ~r2_hidden('#skF_3'('#skF_5', k4_xboole_0(A_634, A_634), '#skF_4'), '#skF_5') | k4_xboole_0('#skF_5', k4_xboole_0(A_634, A_634))='#skF_4')), inference(resolution, [status(thm)], [c_34964, c_14])).
% 14.39/6.08  tff(c_35048, plain, (![A_634]: (r2_hidden('#skF_3'('#skF_5', k4_xboole_0(A_634, A_634), '#skF_4'), k4_xboole_0(A_634, A_634)) | '#skF_5'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3902, c_34372, c_34977])).
% 14.39/6.08  tff(c_35496, plain, (![A_640]: (r2_hidden('#skF_3'('#skF_5', k4_xboole_0(A_640, A_640), '#skF_4'), k4_xboole_0(A_640, A_640)))), inference(negUnitSimplification, [status(thm)], [c_26, c_35048])).
% 14.39/6.08  tff(c_1521, plain, (![A_147]: (r2_hidden('#skF_3'(A_147, '#skF_5', A_147), '#skF_4') | k4_xboole_0(A_147, '#skF_5')=A_147)), inference(resolution, [status(thm)], [c_1495, c_173])).
% 14.39/6.08  tff(c_20680, plain, (![A_505, B_506, B_507]: (~r2_hidden('#skF_3'(k4_xboole_0(A_505, B_506), B_507, k4_xboole_0(A_505, B_506)), B_506) | k4_xboole_0(k4_xboole_0(A_505, B_506), B_507)=k4_xboole_0(A_505, B_506))), inference(resolution, [status(thm)], [c_492, c_10])).
% 14.39/6.08  tff(c_22128, plain, (![A_512]: (k4_xboole_0(k4_xboole_0(A_512, '#skF_4'), '#skF_5')=k4_xboole_0(A_512, '#skF_4'))), inference(resolution, [status(thm)], [c_1521, c_20680])).
% 14.39/6.08  tff(c_22346, plain, (![D_11, A_512]: (~r2_hidden(D_11, '#skF_5') | ~r2_hidden(D_11, k4_xboole_0(A_512, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_22128, c_10])).
% 14.39/6.08  tff(c_35508, plain, (~r2_hidden('#skF_3'('#skF_5', k4_xboole_0('#skF_4', '#skF_4'), '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_35496, c_22346])).
% 14.39/6.08  tff(c_35658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34372, c_35508])).
% 14.39/6.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.39/6.08  
% 14.39/6.08  Inference rules
% 14.39/6.08  ----------------------
% 14.39/6.08  #Ref     : 0
% 14.39/6.08  #Sup     : 8779
% 14.39/6.08  #Fact    : 0
% 14.39/6.08  #Define  : 0
% 14.39/6.08  #Split   : 8
% 14.39/6.08  #Chain   : 0
% 14.39/6.08  #Close   : 0
% 14.39/6.08  
% 14.39/6.08  Ordering : KBO
% 14.39/6.08  
% 14.39/6.08  Simplification rules
% 14.39/6.08  ----------------------
% 14.39/6.08  #Subsume      : 3444
% 14.39/6.08  #Demod        : 8457
% 14.39/6.08  #Tautology    : 2809
% 14.39/6.08  #SimpNegUnit  : 177
% 14.39/6.08  #BackRed      : 40
% 14.39/6.08  
% 14.39/6.08  #Partial instantiations: 0
% 14.39/6.08  #Strategies tried      : 1
% 14.39/6.08  
% 14.39/6.08  Timing (in seconds)
% 14.39/6.08  ----------------------
% 14.66/6.09  Preprocessing        : 0.26
% 14.66/6.09  Parsing              : 0.12
% 14.66/6.09  CNF conversion       : 0.02
% 14.66/6.09  Main loop            : 5.01
% 14.66/6.09  Inferencing          : 0.90
% 14.66/6.09  Reduction            : 2.14
% 14.66/6.09  Demodulation         : 1.72
% 14.66/6.09  BG Simplification    : 0.10
% 14.66/6.09  Subsumption          : 1.63
% 14.66/6.09  Abstraction          : 0.17
% 14.66/6.09  MUC search           : 0.00
% 14.66/6.09  Cooper               : 0.00
% 14.66/6.09  Total                : 5.30
% 14.66/6.09  Index Insertion      : 0.00
% 14.66/6.09  Index Deletion       : 0.00
% 14.66/6.09  Index Matching       : 0.00
% 14.66/6.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
