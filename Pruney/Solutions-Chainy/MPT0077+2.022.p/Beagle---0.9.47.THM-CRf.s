%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:38 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 417 expanded)
%              Number of leaves         :   23 ( 135 expanded)
%              Depth                    :   12
%              Number of atoms          :  178 ( 932 expanded)
%              Number of equality atoms :   45 ( 124 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_63,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_67,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_20])).

tff(c_28,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_82,plain,(
    k3_xboole_0('#skF_7','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_20])).

tff(c_131,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k3_xboole_0(A_38,B_39),k3_xboole_0(A_38,C_40)) = k3_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_152,plain,(
    ! [B_39] : k3_xboole_0('#skF_7',k2_xboole_0(B_39,'#skF_9')) = k2_xboole_0(k3_xboole_0('#skF_7',B_39),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_131])).

tff(c_161,plain,(
    ! [B_39] : k3_xboole_0('#skF_7',k2_xboole_0(B_39,'#skF_9')) = k3_xboole_0('#skF_7',B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_152])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_113,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_117,plain,(
    k3_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_113])).

tff(c_163,plain,(
    k3_xboole_0('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_117])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_163])).

tff(c_168,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_178,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_42])).

tff(c_179,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),k3_xboole_0(A_9,B_10))
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [C_13] :
      ( ~ r1_xboole_0('#skF_7','#skF_8')
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_26])).

tff(c_75,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_71])).

tff(c_167,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_172,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_20])).

tff(c_225,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k3_xboole_0(A_44,B_45),k3_xboole_0(A_44,C_46)) = k3_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_844,plain,(
    ! [D_73,A_74,B_75,C_76] :
      ( ~ r2_hidden(D_73,k3_xboole_0(A_74,B_75))
      | r2_hidden(D_73,k3_xboole_0(A_74,k2_xboole_0(B_75,C_76))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_6])).

tff(c_901,plain,(
    ! [D_73] :
      ( ~ r2_hidden(D_73,k3_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(D_73,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_844])).

tff(c_919,plain,(
    ! [D_77] : ~ r2_hidden(D_77,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_901])).

tff(c_923,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_919])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_923])).

tff(c_928,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_929,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_937,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_929,c_20])).

tff(c_993,plain,(
    ! [A_81,B_82,C_83] : k2_xboole_0(k3_xboole_0(A_81,B_82),k3_xboole_0(A_81,C_83)) = k3_xboole_0(A_81,k2_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1444,plain,(
    ! [C_97] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_97)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_993])).

tff(c_1464,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1444,c_172])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1511,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,k3_xboole_0('#skF_4','#skF_6'))
      | r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1464,c_4])).

tff(c_1521,plain,(
    ! [D_101] : ~ r2_hidden(D_101,k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1511])).

tff(c_1525,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_1521])).

tff(c_1529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_928,c_1525])).

tff(c_1531,plain,(
    ~ r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1554,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1531,c_34])).

tff(c_1555,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1554])).

tff(c_1530,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1540,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1530,c_20])).

tff(c_1589,plain,(
    ! [A_110,B_111,C_112] : k2_xboole_0(k3_xboole_0(A_110,B_111),k3_xboole_0(A_110,C_112)) = k3_xboole_0(A_110,k2_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2091,plain,(
    ! [D_141,A_142,B_143,C_144] :
      ( ~ r2_hidden(D_141,k3_xboole_0(A_142,B_143))
      | r2_hidden(D_141,k3_xboole_0(A_142,k2_xboole_0(B_143,C_144))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1589,c_6])).

tff(c_2136,plain,(
    ! [D_141] :
      ( ~ r2_hidden(D_141,k3_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(D_141,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_2091])).

tff(c_2151,plain,(
    ! [D_145] : ~ r2_hidden(D_145,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2136])).

tff(c_2155,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_2151])).

tff(c_2159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1555,c_2155])).

tff(c_2160,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1554])).

tff(c_2161,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1554])).

tff(c_2170,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2161,c_20])).

tff(c_2215,plain,(
    ! [A_151,B_152,C_153] : k2_xboole_0(k3_xboole_0(A_151,B_152),k3_xboole_0(A_151,C_153)) = k3_xboole_0(A_151,k2_xboole_0(B_152,C_153)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2397,plain,(
    ! [C_161] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_161)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2170,c_2215])).

tff(c_2416,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2397,c_1540])).

tff(c_2445,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,k3_xboole_0('#skF_4','#skF_6'))
      | r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2416,c_4])).

tff(c_2455,plain,(
    ! [D_162] : ~ r2_hidden(D_162,k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2445])).

tff(c_2459,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_2455])).

tff(c_2463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2160,c_2459])).

tff(c_2465,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2502,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2465,c_38])).

tff(c_2503,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2502])).

tff(c_2508,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_2503])).

tff(c_2466,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_2474,plain,(
    k3_xboole_0('#skF_7','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2466,c_20])).

tff(c_2478,plain,(
    ! [C_13] :
      ( ~ r1_xboole_0('#skF_7','#skF_9')
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2474,c_26])).

tff(c_2482,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2466,c_2478])).

tff(c_2464,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2488,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2464,c_20])).

tff(c_2538,plain,(
    ! [A_172,B_173,C_174] : k2_xboole_0(k3_xboole_0(A_172,B_173),k3_xboole_0(A_172,C_174)) = k3_xboole_0(A_172,k2_xboole_0(B_173,C_174)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2774,plain,(
    ! [D_186,A_187,C_188,B_189] :
      ( ~ r2_hidden(D_186,k3_xboole_0(A_187,C_188))
      | r2_hidden(D_186,k3_xboole_0(A_187,k2_xboole_0(B_189,C_188))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2538,c_4])).

tff(c_2802,plain,(
    ! [D_186] :
      ( ~ r2_hidden(D_186,k3_xboole_0('#skF_4','#skF_6'))
      | r2_hidden(D_186,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_2774])).

tff(c_2851,plain,(
    ! [D_191] : ~ r2_hidden(D_191,k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2482,c_2802])).

tff(c_2856,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_2851])).

tff(c_2860,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2856,c_20])).

tff(c_30,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(A_15,C_17)) = k3_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2868,plain,(
    ! [B_16] : k3_xboole_0('#skF_4',k2_xboole_0(B_16,'#skF_6')) = k2_xboole_0(k3_xboole_0('#skF_4',B_16),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2860,c_30])).

tff(c_2956,plain,(
    ! [B_196] : k3_xboole_0('#skF_4',k2_xboole_0(B_196,'#skF_6')) = k3_xboole_0('#skF_4',B_196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2868])).

tff(c_2978,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2956,c_2488])).

tff(c_2998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2508,c_2978])).

tff(c_2999,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2502])).

tff(c_3000,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2502])).

tff(c_3009,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3000,c_20])).

tff(c_3055,plain,(
    ! [A_202,B_203,C_204] : k2_xboole_0(k3_xboole_0(A_202,B_203),k3_xboole_0(A_202,C_204)) = k3_xboole_0(A_202,k2_xboole_0(B_203,C_204)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3258,plain,(
    ! [C_213] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_213)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3009,c_3055])).

tff(c_3281,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3258,c_2488])).

tff(c_3316,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,k3_xboole_0('#skF_4','#skF_6'))
      | r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3281,c_4])).

tff(c_3326,plain,(
    ! [D_214] : ~ r2_hidden(D_214,k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2482,c_3316])).

tff(c_3330,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_3326])).

tff(c_3334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2999,c_3330])).

tff(c_3336,plain,(
    ~ r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_3360,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_3336,c_34])).

tff(c_3361,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3360])).

tff(c_3348,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2464,c_20])).

tff(c_3353,plain,(
    ! [C_13] :
      ( ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3348,c_26])).

tff(c_3357,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2464,c_3353])).

tff(c_3395,plain,(
    ! [A_224,B_225,C_226] : k2_xboole_0(k3_xboole_0(A_224,B_225),k3_xboole_0(A_224,C_226)) = k3_xboole_0(A_224,k2_xboole_0(B_225,C_226)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3574,plain,(
    ! [D_234,A_235,B_236,C_237] :
      ( ~ r2_hidden(D_234,k3_xboole_0(A_235,B_236))
      | r2_hidden(D_234,k3_xboole_0(A_235,k2_xboole_0(B_236,C_237))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3395,c_6])).

tff(c_3595,plain,(
    ! [D_234] :
      ( ~ r2_hidden(D_234,k3_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(D_234,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3348,c_3574])).

tff(c_3604,plain,(
    ! [D_238] : ~ r2_hidden(D_238,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3357,c_3595])).

tff(c_3608,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_3604])).

tff(c_3612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3361,c_3608])).

tff(c_3613,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_3360])).

tff(c_3614,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3360])).

tff(c_3615,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2465,c_38])).

tff(c_3616,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3615])).

tff(c_3626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_3616])).

tff(c_3628,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3615])).

tff(c_3636,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3628,c_20])).

tff(c_3682,plain,(
    ! [A_247,B_248,C_249] : k2_xboole_0(k3_xboole_0(A_247,B_248),k3_xboole_0(A_247,C_249)) = k3_xboole_0(A_247,k2_xboole_0(B_248,C_249)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3769,plain,(
    ! [C_255] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_255)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3636,c_3682])).

tff(c_3792,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_3348])).

tff(c_3827,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,k3_xboole_0('#skF_4','#skF_6'))
      | r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3792,c_4])).

tff(c_3837,plain,(
    ! [D_256] : ~ r2_hidden(D_256,k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_3357,c_3827])).

tff(c_3841,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_3837])).

tff(c_3845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3613,c_3841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:52:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.81  
% 4.45/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.81  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 4.45/1.81  
% 4.45/1.81  %Foreground sorts:
% 4.45/1.81  
% 4.45/1.81  
% 4.45/1.81  %Background operators:
% 4.45/1.81  
% 4.45/1.81  
% 4.45/1.81  %Foreground operators:
% 4.45/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.45/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.45/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.45/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.45/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.45/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.45/1.81  tff('#skF_9', type, '#skF_9': $i).
% 4.45/1.81  tff('#skF_8', type, '#skF_8': $i).
% 4.45/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/1.81  
% 4.50/1.83  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.50/1.83  tff(f_73, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.50/1.83  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.50/1.83  tff(f_56, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 4.50/1.83  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.50/1.83  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.50/1.83  tff(c_22, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.50/1.83  tff(c_36, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.83  tff(c_63, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_36])).
% 4.50/1.83  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.50/1.83  tff(c_67, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_20])).
% 4.50/1.83  tff(c_28, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.50/1.83  tff(c_32, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | r1_xboole_0('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.83  tff(c_78, plain, (r1_xboole_0('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_32])).
% 4.50/1.83  tff(c_82, plain, (k3_xboole_0('#skF_7', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_20])).
% 4.50/1.83  tff(c_131, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k3_xboole_0(A_38, B_39), k3_xboole_0(A_38, C_40))=k3_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_152, plain, (![B_39]: (k3_xboole_0('#skF_7', k2_xboole_0(B_39, '#skF_9'))=k2_xboole_0(k3_xboole_0('#skF_7', B_39), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_131])).
% 4.50/1.83  tff(c_161, plain, (![B_39]: (k3_xboole_0('#skF_7', k2_xboole_0(B_39, '#skF_9'))=k3_xboole_0('#skF_7', B_39))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_152])).
% 4.50/1.83  tff(c_40, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | ~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.83  tff(c_113, plain, (~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_40])).
% 4.50/1.83  tff(c_117, plain, (k3_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_113])).
% 4.50/1.83  tff(c_163, plain, (k3_xboole_0('#skF_7', '#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_161, c_117])).
% 4.50/1.83  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_163])).
% 4.50/1.83  tff(c_168, plain, (r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_40])).
% 4.50/1.83  tff(c_42, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.83  tff(c_178, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_42])).
% 4.50/1.83  tff(c_179, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_178])).
% 4.50/1.83  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), k3_xboole_0(A_9, B_10)) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.50/1.83  tff(c_26, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.50/1.83  tff(c_71, plain, (![C_13]: (~r1_xboole_0('#skF_7', '#skF_8') | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_67, c_26])).
% 4.50/1.83  tff(c_75, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_71])).
% 4.50/1.83  tff(c_167, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_40])).
% 4.50/1.83  tff(c_172, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_167, c_20])).
% 4.50/1.83  tff(c_225, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k3_xboole_0(A_44, B_45), k3_xboole_0(A_44, C_46))=k3_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.50/1.83  tff(c_844, plain, (![D_73, A_74, B_75, C_76]: (~r2_hidden(D_73, k3_xboole_0(A_74, B_75)) | r2_hidden(D_73, k3_xboole_0(A_74, k2_xboole_0(B_75, C_76))))), inference(superposition, [status(thm), theory('equality')], [c_225, c_6])).
% 4.50/1.83  tff(c_901, plain, (![D_73]: (~r2_hidden(D_73, k3_xboole_0('#skF_4', '#skF_5')) | r2_hidden(D_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_172, c_844])).
% 4.50/1.83  tff(c_919, plain, (![D_77]: (~r2_hidden(D_77, k3_xboole_0('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_75, c_901])).
% 4.50/1.83  tff(c_923, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_919])).
% 4.50/1.83  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_923])).
% 4.50/1.83  tff(c_928, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_178])).
% 4.50/1.83  tff(c_929, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_178])).
% 4.50/1.83  tff(c_937, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_929, c_20])).
% 4.50/1.83  tff(c_993, plain, (![A_81, B_82, C_83]: (k2_xboole_0(k3_xboole_0(A_81, B_82), k3_xboole_0(A_81, C_83))=k3_xboole_0(A_81, k2_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_1444, plain, (![C_97]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_97))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_97)))), inference(superposition, [status(thm), theory('equality')], [c_937, c_993])).
% 4.50/1.83  tff(c_1464, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1444, c_172])).
% 4.50/1.83  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.50/1.83  tff(c_1511, plain, (![D_6]: (~r2_hidden(D_6, k3_xboole_0('#skF_4', '#skF_6')) | r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1464, c_4])).
% 4.50/1.83  tff(c_1521, plain, (![D_101]: (~r2_hidden(D_101, k3_xboole_0('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_75, c_1511])).
% 4.50/1.83  tff(c_1525, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_1521])).
% 4.50/1.83  tff(c_1529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_928, c_1525])).
% 4.50/1.83  tff(c_1531, plain, (~r1_xboole_0('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_32])).
% 4.50/1.83  tff(c_34, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.83  tff(c_1554, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1531, c_34])).
% 4.50/1.83  tff(c_1555, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1554])).
% 4.50/1.83  tff(c_1530, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_32])).
% 4.50/1.83  tff(c_1540, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1530, c_20])).
% 4.50/1.83  tff(c_1589, plain, (![A_110, B_111, C_112]: (k2_xboole_0(k3_xboole_0(A_110, B_111), k3_xboole_0(A_110, C_112))=k3_xboole_0(A_110, k2_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_2091, plain, (![D_141, A_142, B_143, C_144]: (~r2_hidden(D_141, k3_xboole_0(A_142, B_143)) | r2_hidden(D_141, k3_xboole_0(A_142, k2_xboole_0(B_143, C_144))))), inference(superposition, [status(thm), theory('equality')], [c_1589, c_6])).
% 4.50/1.83  tff(c_2136, plain, (![D_141]: (~r2_hidden(D_141, k3_xboole_0('#skF_4', '#skF_5')) | r2_hidden(D_141, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1540, c_2091])).
% 4.50/1.83  tff(c_2151, plain, (![D_145]: (~r2_hidden(D_145, k3_xboole_0('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_75, c_2136])).
% 4.50/1.83  tff(c_2155, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_2151])).
% 4.50/1.83  tff(c_2159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1555, c_2155])).
% 4.50/1.83  tff(c_2160, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_1554])).
% 4.50/1.83  tff(c_2161, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1554])).
% 4.50/1.83  tff(c_2170, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2161, c_20])).
% 4.50/1.83  tff(c_2215, plain, (![A_151, B_152, C_153]: (k2_xboole_0(k3_xboole_0(A_151, B_152), k3_xboole_0(A_151, C_153))=k3_xboole_0(A_151, k2_xboole_0(B_152, C_153)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_2397, plain, (![C_161]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_161))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_161)))), inference(superposition, [status(thm), theory('equality')], [c_2170, c_2215])).
% 4.50/1.83  tff(c_2416, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2397, c_1540])).
% 4.50/1.83  tff(c_2445, plain, (![D_6]: (~r2_hidden(D_6, k3_xboole_0('#skF_4', '#skF_6')) | r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2416, c_4])).
% 4.50/1.83  tff(c_2455, plain, (![D_162]: (~r2_hidden(D_162, k3_xboole_0('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_75, c_2445])).
% 4.50/1.83  tff(c_2459, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_2455])).
% 4.50/1.83  tff(c_2463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2160, c_2459])).
% 4.50/1.83  tff(c_2465, plain, (~r1_xboole_0('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_36])).
% 4.50/1.83  tff(c_38, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.83  tff(c_2502, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2465, c_38])).
% 4.50/1.83  tff(c_2503, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2502])).
% 4.50/1.83  tff(c_2508, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_2503])).
% 4.50/1.83  tff(c_2466, plain, (r1_xboole_0('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_32])).
% 4.50/1.83  tff(c_2474, plain, (k3_xboole_0('#skF_7', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_2466, c_20])).
% 4.50/1.83  tff(c_2478, plain, (![C_13]: (~r1_xboole_0('#skF_7', '#skF_9') | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2474, c_26])).
% 4.50/1.83  tff(c_2482, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2466, c_2478])).
% 4.50/1.83  tff(c_2464, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_36])).
% 4.50/1.83  tff(c_2488, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2464, c_20])).
% 4.50/1.83  tff(c_2538, plain, (![A_172, B_173, C_174]: (k2_xboole_0(k3_xboole_0(A_172, B_173), k3_xboole_0(A_172, C_174))=k3_xboole_0(A_172, k2_xboole_0(B_173, C_174)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_2774, plain, (![D_186, A_187, C_188, B_189]: (~r2_hidden(D_186, k3_xboole_0(A_187, C_188)) | r2_hidden(D_186, k3_xboole_0(A_187, k2_xboole_0(B_189, C_188))))), inference(superposition, [status(thm), theory('equality')], [c_2538, c_4])).
% 4.50/1.83  tff(c_2802, plain, (![D_186]: (~r2_hidden(D_186, k3_xboole_0('#skF_4', '#skF_6')) | r2_hidden(D_186, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2488, c_2774])).
% 4.50/1.83  tff(c_2851, plain, (![D_191]: (~r2_hidden(D_191, k3_xboole_0('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_2482, c_2802])).
% 4.50/1.83  tff(c_2856, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_2851])).
% 4.50/1.83  tff(c_2860, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2856, c_20])).
% 4.50/1.83  tff(c_30, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k3_xboole_0(A_15, B_16), k3_xboole_0(A_15, C_17))=k3_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_2868, plain, (![B_16]: (k3_xboole_0('#skF_4', k2_xboole_0(B_16, '#skF_6'))=k2_xboole_0(k3_xboole_0('#skF_4', B_16), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2860, c_30])).
% 4.50/1.83  tff(c_2956, plain, (![B_196]: (k3_xboole_0('#skF_4', k2_xboole_0(B_196, '#skF_6'))=k3_xboole_0('#skF_4', B_196))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2868])).
% 4.50/1.83  tff(c_2978, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2956, c_2488])).
% 4.50/1.83  tff(c_2998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2508, c_2978])).
% 4.50/1.83  tff(c_2999, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_2502])).
% 4.50/1.83  tff(c_3000, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2502])).
% 4.50/1.83  tff(c_3009, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3000, c_20])).
% 4.50/1.83  tff(c_3055, plain, (![A_202, B_203, C_204]: (k2_xboole_0(k3_xboole_0(A_202, B_203), k3_xboole_0(A_202, C_204))=k3_xboole_0(A_202, k2_xboole_0(B_203, C_204)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_3258, plain, (![C_213]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_213))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_213)))), inference(superposition, [status(thm), theory('equality')], [c_3009, c_3055])).
% 4.50/1.83  tff(c_3281, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3258, c_2488])).
% 4.50/1.83  tff(c_3316, plain, (![D_6]: (~r2_hidden(D_6, k3_xboole_0('#skF_4', '#skF_6')) | r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3281, c_4])).
% 4.50/1.83  tff(c_3326, plain, (![D_214]: (~r2_hidden(D_214, k3_xboole_0('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_2482, c_3316])).
% 4.50/1.83  tff(c_3330, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_3326])).
% 4.50/1.83  tff(c_3334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2999, c_3330])).
% 4.50/1.83  tff(c_3336, plain, (~r1_xboole_0('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_32])).
% 4.50/1.83  tff(c_3360, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_3336, c_34])).
% 4.50/1.83  tff(c_3361, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3360])).
% 4.50/1.83  tff(c_3348, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2464, c_20])).
% 4.50/1.83  tff(c_3353, plain, (![C_13]: (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3348, c_26])).
% 4.50/1.83  tff(c_3357, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2464, c_3353])).
% 4.50/1.83  tff(c_3395, plain, (![A_224, B_225, C_226]: (k2_xboole_0(k3_xboole_0(A_224, B_225), k3_xboole_0(A_224, C_226))=k3_xboole_0(A_224, k2_xboole_0(B_225, C_226)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_3574, plain, (![D_234, A_235, B_236, C_237]: (~r2_hidden(D_234, k3_xboole_0(A_235, B_236)) | r2_hidden(D_234, k3_xboole_0(A_235, k2_xboole_0(B_236, C_237))))), inference(superposition, [status(thm), theory('equality')], [c_3395, c_6])).
% 4.50/1.83  tff(c_3595, plain, (![D_234]: (~r2_hidden(D_234, k3_xboole_0('#skF_4', '#skF_5')) | r2_hidden(D_234, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3348, c_3574])).
% 4.50/1.83  tff(c_3604, plain, (![D_238]: (~r2_hidden(D_238, k3_xboole_0('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_3357, c_3595])).
% 4.50/1.83  tff(c_3608, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_3604])).
% 4.50/1.83  tff(c_3612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3361, c_3608])).
% 4.50/1.83  tff(c_3613, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_3360])).
% 4.50/1.83  tff(c_3614, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_3360])).
% 4.50/1.83  tff(c_3615, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2465, c_38])).
% 4.50/1.83  tff(c_3616, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3615])).
% 4.50/1.83  tff(c_3626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3614, c_3616])).
% 4.50/1.83  tff(c_3628, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_3615])).
% 4.50/1.83  tff(c_3636, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3628, c_20])).
% 4.50/1.83  tff(c_3682, plain, (![A_247, B_248, C_249]: (k2_xboole_0(k3_xboole_0(A_247, B_248), k3_xboole_0(A_247, C_249))=k3_xboole_0(A_247, k2_xboole_0(B_248, C_249)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.83  tff(c_3769, plain, (![C_255]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_255))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_255)))), inference(superposition, [status(thm), theory('equality')], [c_3636, c_3682])).
% 4.50/1.83  tff(c_3792, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3769, c_3348])).
% 4.50/1.83  tff(c_3827, plain, (![D_6]: (~r2_hidden(D_6, k3_xboole_0('#skF_4', '#skF_6')) | r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3792, c_4])).
% 4.50/1.83  tff(c_3837, plain, (![D_256]: (~r2_hidden(D_256, k3_xboole_0('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_3357, c_3827])).
% 4.50/1.83  tff(c_3841, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_3837])).
% 4.50/1.83  tff(c_3845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3613, c_3841])).
% 4.50/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.83  
% 4.50/1.83  Inference rules
% 4.50/1.83  ----------------------
% 4.50/1.83  #Ref     : 0
% 4.50/1.83  #Sup     : 943
% 4.50/1.83  #Fact    : 0
% 4.50/1.83  #Define  : 0
% 4.50/1.83  #Split   : 9
% 4.50/1.83  #Chain   : 0
% 4.50/1.83  #Close   : 0
% 4.50/1.83  
% 4.50/1.83  Ordering : KBO
% 4.50/1.83  
% 4.50/1.83  Simplification rules
% 4.50/1.83  ----------------------
% 4.50/1.83  #Subsume      : 120
% 4.50/1.83  #Demod        : 530
% 4.50/1.83  #Tautology    : 404
% 4.50/1.83  #SimpNegUnit  : 104
% 4.50/1.83  #BackRed      : 24
% 4.50/1.83  
% 4.50/1.83  #Partial instantiations: 0
% 4.50/1.83  #Strategies tried      : 1
% 4.50/1.83  
% 4.50/1.83  Timing (in seconds)
% 4.50/1.83  ----------------------
% 4.50/1.83  Preprocessing        : 0.28
% 4.50/1.83  Parsing              : 0.15
% 4.50/1.83  CNF conversion       : 0.02
% 4.50/1.83  Main loop            : 0.76
% 4.50/1.83  Inferencing          : 0.28
% 4.50/1.83  Reduction            : 0.26
% 4.50/1.84  Demodulation         : 0.19
% 4.50/1.84  BG Simplification    : 0.03
% 4.50/1.84  Subsumption          : 0.12
% 4.50/1.84  Abstraction          : 0.04
% 4.50/1.84  MUC search           : 0.00
% 4.50/1.84  Cooper               : 0.00
% 4.50/1.84  Total                : 1.11
% 4.50/1.84  Index Insertion      : 0.00
% 4.50/1.84  Index Deletion       : 0.00
% 4.50/1.84  Index Matching       : 0.00
% 4.50/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
