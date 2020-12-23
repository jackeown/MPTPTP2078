%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0730+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:46 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 164 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 295 expanded)
%              Number of equality atoms :   25 (  93 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_26,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,k1_ordinal1(B))
      <=> ( r2_hidden(A,B)
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_tarski(A_1)) = k1_ordinal1(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_312,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | r2_hidden(D_76,k2_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_327,plain,(
    ! [D_84,A_85] :
      ( ~ r2_hidden(D_84,k1_tarski(A_85))
      | r2_hidden(D_84,k1_ordinal1(A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_312])).

tff(c_331,plain,(
    ! [C_6] : r2_hidden(C_6,k1_ordinal1(C_6)) ),
    inference(resolution,[status(thm)],[c_6,c_327])).

tff(c_227,plain,(
    ! [D_58,B_59,A_60] :
      ( ~ r2_hidden(D_58,B_59)
      | r2_hidden(D_58,k2_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_266,plain,(
    ! [D_71,A_72] :
      ( ~ r2_hidden(D_71,k1_tarski(A_72))
      | r2_hidden(D_71,k1_ordinal1(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_270,plain,(
    ! [C_6] : r2_hidden(C_6,k1_ordinal1(C_6)) ),
    inference(resolution,[status(thm)],[c_6,c_266])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_63,plain,(
    ! [D_17,B_18,A_19] :
      ( ~ r2_hidden(D_17,B_18)
      | r2_hidden(D_17,k2_xboole_0(A_19,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_139,plain,(
    ! [D_37,A_38] :
      ( ~ r2_hidden(D_37,k1_tarski(A_38))
      | r2_hidden(D_37,k1_ordinal1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_63])).

tff(c_143,plain,(
    ! [C_6] : r2_hidden(C_6,k1_ordinal1(C_6)) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_68,plain,(
    ! [D_20,A_21,B_22] :
      ( ~ r2_hidden(D_20,A_21)
      | r2_hidden(D_20,k2_xboole_0(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    ! [D_23,A_24] :
      ( ~ r2_hidden(D_23,A_24)
      | r2_hidden(D_23,k1_ordinal1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_67])).

tff(c_44,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_44])).

tff(c_78,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_86,plain,(
    ! [D_30,B_31,A_32] :
      ( r2_hidden(D_30,B_31)
      | r2_hidden(D_30,A_32)
      | ~ r2_hidden(D_30,k2_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [D_33,A_34] :
      ( r2_hidden(D_33,k1_tarski(A_34))
      | r2_hidden(D_33,A_34)
      | ~ r2_hidden(D_33,k1_ordinal1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [D_35,A_36] :
      ( D_35 = A_36
      | r2_hidden(D_35,A_36)
      | ~ r2_hidden(D_35,k1_ordinal1(A_36)) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_113,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_107])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_113])).

tff(c_123,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_67])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_126])).

tff(c_147,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_162,plain,(
    ! [D_49,B_50,A_51] :
      ( r2_hidden(D_49,B_50)
      | r2_hidden(D_49,A_51)
      | ~ r2_hidden(D_49,k2_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [D_54,A_55] :
      ( r2_hidden(D_54,k1_tarski(A_55))
      | r2_hidden(D_54,A_55)
      | ~ r2_hidden(D_54,k1_ordinal1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_162])).

tff(c_199,plain,(
    ! [D_56,A_57] :
      ( D_56 = A_57
      | r2_hidden(D_56,A_57)
      | ~ r2_hidden(D_56,k1_ordinal1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_215,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_147,c_199])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_215])).

tff(c_226,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_232,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_40])).

tff(c_233,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_234,plain,(
    ! [D_61,A_62,B_63] :
      ( ~ r2_hidden(D_61,A_62)
      | r2_hidden(D_61,k2_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_239,plain,(
    ! [D_64,A_65] :
      ( ~ r2_hidden(D_64,A_65)
      | r2_hidden(D_64,k1_ordinal1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_234])).

tff(c_225,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_242,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_239,c_225])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_242])).

tff(c_247,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_249,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_225])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_249])).

tff(c_275,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6')
    | '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_276,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_276])).

tff(c_283,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_290,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_274,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_291,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_274])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_291])).

tff(c_335,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_360,plain,(
    ! [D_92,A_93,B_94] :
      ( ~ r2_hidden(D_92,A_93)
      | r2_hidden(D_92,k2_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_364,plain,(
    ! [D_95,A_96] :
      ( ~ r2_hidden(D_95,A_96)
      | r2_hidden(D_95,k1_ordinal1(A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_360])).

tff(c_367,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_364,c_274])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_367])).

%------------------------------------------------------------------------------
