%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0469+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:21 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 136 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 226 expanded)
%              Number of equality atoms :   21 (  59 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_543,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(k4_tarski('#skF_1'(A_109,B_110),'#skF_2'(A_109,B_110)),A_109)
      | r2_hidden('#skF_3'(A_109,B_110),B_110)
      | k1_relat_1(A_109) = B_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [B_41,A_40] :
      ( ~ v1_xboole_0(B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1404,plain,(
    ! [A_145,B_146] :
      ( ~ v1_xboole_0(A_145)
      | r2_hidden('#skF_3'(A_145,B_146),B_146)
      | k1_relat_1(A_145) = B_146 ) ),
    inference(resolution,[status(thm)],[c_543,c_30])).

tff(c_744,plain,(
    ! [A_117,B_118] :
      ( r2_hidden(k4_tarski('#skF_6'(A_117,B_118),'#skF_5'(A_117,B_118)),A_117)
      | r2_hidden('#skF_7'(A_117,B_118),B_118)
      | k2_relat_1(A_117) = B_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1104,plain,(
    ! [A_136,B_137] :
      ( ~ v1_xboole_0(A_136)
      | r2_hidden('#skF_7'(A_136,B_137),B_137)
      | k2_relat_1(A_136) = B_137 ) ),
    inference(resolution,[status(thm)],[c_744,c_30])).

tff(c_1274,plain,(
    ! [B_141,A_142] :
      ( ~ v1_xboole_0(B_141)
      | ~ v1_xboole_0(A_142)
      | k2_relat_1(A_142) = B_141 ) ),
    inference(resolution,[status(thm)],[c_1104,c_30])).

tff(c_1278,plain,(
    ! [A_143] :
      ( ~ v1_xboole_0(A_143)
      | k2_relat_1(A_143) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_1274])).

tff(c_1282,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1278])).

tff(c_14,plain,(
    ! [A_20,C_35] :
      ( r2_hidden(k4_tarski('#skF_8'(A_20,k2_relat_1(A_20),C_35),C_35),A_20)
      | ~ r2_hidden(C_35,k2_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_67,C_68] :
      ( r2_hidden(k4_tarski('#skF_8'(A_67,k2_relat_1(A_67),C_68),C_68),A_67)
      | ~ r2_hidden(C_68,k2_relat_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_170,plain,(
    ! [A_69,C_70] :
      ( ~ v1_xboole_0(A_69)
      | ~ r2_hidden(C_70,k2_relat_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_127,c_30])).

tff(c_202,plain,(
    ! [A_73,C_74] :
      ( ~ v1_xboole_0(A_73)
      | ~ r2_hidden(C_74,k2_relat_1(k2_relat_1(A_73))) ) ),
    inference(resolution,[status(thm)],[c_14,c_170])).

tff(c_331,plain,(
    ! [A_83,C_84] :
      ( ~ v1_xboole_0(A_83)
      | ~ r2_hidden(C_84,k2_relat_1(k2_relat_1(k2_relat_1(A_83)))) ) ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_349,plain,(
    ! [A_83,C_35] :
      ( ~ v1_xboole_0(A_83)
      | ~ r2_hidden(C_35,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_83))))) ) ),
    inference(resolution,[status(thm)],[c_14,c_331])).

tff(c_1301,plain,(
    ! [C_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_35,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_349])).

tff(c_1345,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_1282,c_1282,c_26,c_1301])).

tff(c_1785,plain,(
    ! [A_152] :
      ( ~ v1_xboole_0(A_152)
      | k1_relat_1(A_152) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1404,c_1345])).

tff(c_1788,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1785])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1788])).

tff(c_1793,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2618,plain,(
    ! [A_221,B_222] :
      ( r2_hidden(k4_tarski('#skF_6'(A_221,B_222),'#skF_5'(A_221,B_222)),A_221)
      | r2_hidden('#skF_7'(A_221,B_222),B_222)
      | k2_relat_1(A_221) = B_222 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1794,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1801,plain,(
    ! [C_159,A_160] :
      ( r2_hidden(k4_tarski(C_159,'#skF_4'(A_160,k1_relat_1(A_160),C_159)),A_160)
      | ~ r2_hidden(C_159,k1_relat_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1818,plain,(
    ! [A_161,C_162] :
      ( ~ v1_xboole_0(A_161)
      | ~ r2_hidden(C_162,k1_relat_1(A_161)) ) ),
    inference(resolution,[status(thm)],[c_1801,c_30])).

tff(c_1825,plain,(
    ! [C_162] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_162,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1794,c_1818])).

tff(c_1828,plain,(
    ! [C_162] : ~ r2_hidden(C_162,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1825])).

tff(c_2884,plain,(
    ! [B_229] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_229),B_229)
      | k2_relat_1(k1_xboole_0) = B_229 ) ),
    inference(resolution,[status(thm)],[c_2618,c_1828])).

tff(c_3016,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2884,c_1828])).

tff(c_3060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1793,c_3016])).

%------------------------------------------------------------------------------
