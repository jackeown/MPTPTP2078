%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:20 EST 2020

% Result     : Theorem 26.66s
% Output     : CNFRefutation 26.66s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 173 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 296 expanded)
%              Number of equality atoms :   34 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_264,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4758,plain,(
    ! [A_213,B_214,B_215] :
      ( r2_hidden('#skF_1'(A_213,B_214),B_215)
      | ~ r1_tarski(A_213,B_215)
      | r1_tarski(A_213,B_214) ) ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63748,plain,(
    ! [A_1005,B_1006,A_1007,B_1008] :
      ( r2_hidden('#skF_1'(A_1005,B_1006),A_1007)
      | ~ r1_tarski(A_1005,k4_xboole_0(A_1007,B_1008))
      | r1_tarski(A_1005,B_1006) ) ),
    inference(resolution,[status(thm)],[c_4758,c_12])).

tff(c_63841,plain,(
    ! [B_1009] :
      ( r2_hidden('#skF_1'('#skF_4',B_1009),'#skF_5')
      | r1_tarski('#skF_4',B_1009) ) ),
    inference(resolution,[status(thm)],[c_46,c_63748])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63850,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_63841,c_4])).

tff(c_63856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_63850])).

tff(c_63857,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_30,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_64011,plain,(
    ! [A_1033,B_1034] :
      ( r2_hidden('#skF_1'(A_1033,B_1034),A_1033)
      | r1_tarski(A_1033,B_1034) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72832,plain,(
    ! [A_1254,B_1255,B_1256] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_1254,B_1255),B_1256),A_1254)
      | r1_tarski(k4_xboole_0(A_1254,B_1255),B_1256) ) ),
    inference(resolution,[status(thm)],[c_64011,c_12])).

tff(c_72943,plain,(
    ! [A_1257,B_1258] : r1_tarski(k4_xboole_0(A_1257,B_1258),A_1257) ),
    inference(resolution,[status(thm)],[c_72832,c_4])).

tff(c_72970,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_72943])).

tff(c_64679,plain,(
    ! [D_1069,A_1070,B_1071] :
      ( r2_hidden(D_1069,k4_xboole_0(A_1070,B_1071))
      | r2_hidden(D_1069,B_1071)
      | ~ r2_hidden(D_1069,A_1070) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93930,plain,(
    ! [A_1500,A_1501,B_1502] :
      ( r1_tarski(A_1500,k4_xboole_0(A_1501,B_1502))
      | r2_hidden('#skF_1'(A_1500,k4_xboole_0(A_1501,B_1502)),B_1502)
      | ~ r2_hidden('#skF_1'(A_1500,k4_xboole_0(A_1501,B_1502)),A_1501) ) ),
    inference(resolution,[status(thm)],[c_64679,c_4])).

tff(c_94006,plain,(
    ! [A_1,B_1502] :
      ( r2_hidden('#skF_1'(A_1,k4_xboole_0(A_1,B_1502)),B_1502)
      | r1_tarski(A_1,k4_xboole_0(A_1,B_1502)) ) ),
    inference(resolution,[status(thm)],[c_6,c_93930])).

tff(c_64048,plain,(
    ! [C_1039,B_1040,A_1041] :
      ( r2_hidden(C_1039,B_1040)
      | ~ r2_hidden(C_1039,A_1041)
      | ~ r1_tarski(A_1041,B_1040) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68373,plain,(
    ! [A_1187,B_1188,B_1189] :
      ( r2_hidden('#skF_1'(A_1187,B_1188),B_1189)
      | ~ r1_tarski(A_1187,B_1189)
      | r1_tarski(A_1187,B_1188) ) ),
    inference(resolution,[status(thm)],[c_6,c_64048])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_119927,plain,(
    ! [A_1933,B_1934,B_1935,A_1936] :
      ( ~ r2_hidden('#skF_1'(A_1933,B_1934),B_1935)
      | ~ r1_tarski(A_1933,k4_xboole_0(A_1936,B_1935))
      | r1_tarski(A_1933,B_1934) ) ),
    inference(resolution,[status(thm)],[c_68373,c_10])).

tff(c_135160,plain,(
    ! [A_2101,A_2102,B_2103] :
      ( ~ r1_tarski(A_2101,k4_xboole_0(A_2102,B_2103))
      | r1_tarski(A_2101,k4_xboole_0(A_2101,B_2103)) ) ),
    inference(resolution,[status(thm)],[c_94006,c_119927])).

tff(c_135256,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_135160])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68408,plain,(
    ! [A_1187,B_1188,B_2,B_1189] :
      ( r2_hidden('#skF_1'(A_1187,B_1188),B_2)
      | ~ r1_tarski(B_1189,B_2)
      | ~ r1_tarski(A_1187,B_1189)
      | r1_tarski(A_1187,B_1188) ) ),
    inference(resolution,[status(thm)],[c_68373,c_2])).

tff(c_142090,plain,(
    ! [A_2138,B_2139] :
      ( r2_hidden('#skF_1'(A_2138,B_2139),k4_xboole_0('#skF_4','#skF_6'))
      | ~ r1_tarski(A_2138,'#skF_4')
      | r1_tarski(A_2138,B_2139) ) ),
    inference(resolution,[status(thm)],[c_135256,c_68408])).

tff(c_68772,plain,(
    ! [A_1202,B_1203,B_1204] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_1202,B_1203),B_1204),B_1203)
      | r1_tarski(k4_xboole_0(A_1202,B_1203),B_1204) ) ),
    inference(resolution,[status(thm)],[c_64011,c_10])).

tff(c_68801,plain,(
    ! [A_16,B_17,B_1204] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_16,B_17),B_1204),k4_xboole_0(A_16,B_17))
      | r1_tarski(k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)),B_1204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_68772])).

tff(c_68813,plain,(
    ! [A_16,B_17,B_1204] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_16,B_17),B_1204),k4_xboole_0(A_16,B_17))
      | r1_tarski(k3_xboole_0(A_16,B_17),B_1204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68801])).

tff(c_142094,plain,(
    ! [B_2139] :
      ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_4')
      | r1_tarski(k3_xboole_0('#skF_4','#skF_6'),B_2139) ) ),
    inference(resolution,[status(thm)],[c_142090,c_68813])).

tff(c_142136,plain,(
    ! [B_2140] : r1_tarski(k3_xboole_0('#skF_4','#skF_6'),B_2140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72970,c_142094])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63865,plain,(
    ! [A_1017,B_1018] : k4_xboole_0(A_1017,k4_xboole_0(A_1017,B_1018)) = k3_xboole_0(A_1017,B_1018) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63886,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_63865])).

tff(c_63889,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_63886])).

tff(c_65144,plain,(
    ! [A_1090,B_1091,C_1092] :
      ( r2_hidden('#skF_2'(A_1090,B_1091,C_1092),A_1090)
      | r2_hidden('#skF_3'(A_1090,B_1091,C_1092),C_1092)
      | k4_xboole_0(A_1090,B_1091) = C_1092 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65147,plain,(
    ! [A_1090,C_1092] :
      ( r2_hidden('#skF_3'(A_1090,A_1090,C_1092),C_1092)
      | k4_xboole_0(A_1090,A_1090) = C_1092 ) ),
    inference(resolution,[status(thm)],[c_65144,c_22])).

tff(c_65200,plain,(
    ! [A_1093,C_1094] :
      ( r2_hidden('#skF_3'(A_1093,A_1093,C_1094),C_1094)
      | k1_xboole_0 = C_1094 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63889,c_65147])).

tff(c_65221,plain,(
    ! [A_1093,C_1094,B_2] :
      ( r2_hidden('#skF_3'(A_1093,A_1093,C_1094),B_2)
      | ~ r1_tarski(C_1094,B_2)
      | k1_xboole_0 = C_1094 ) ),
    inference(resolution,[status(thm)],[c_65200,c_2])).

tff(c_117010,plain,(
    ! [A_1880,A_1881,B_1882] :
      ( ~ r2_hidden('#skF_3'(A_1880,A_1880,k4_xboole_0(A_1881,B_1882)),B_1882)
      | k4_xboole_0(A_1881,B_1882) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_65200,c_10])).

tff(c_117110,plain,(
    ! [A_1880,A_15] :
      ( ~ r2_hidden('#skF_3'(A_1880,A_1880,A_15),k1_xboole_0)
      | k4_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_117010])).

tff(c_117144,plain,(
    ! [A_1883,A_1884] :
      ( ~ r2_hidden('#skF_3'(A_1883,A_1883,A_1884),k1_xboole_0)
      | k1_xboole_0 = A_1884 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_117110])).

tff(c_117193,plain,(
    ! [C_1094] :
      ( ~ r1_tarski(C_1094,k1_xboole_0)
      | k1_xboole_0 = C_1094 ) ),
    inference(resolution,[status(thm)],[c_65221,c_117144])).

tff(c_142194,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142136,c_117193])).

tff(c_26,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63890,plain,(
    ! [A_1019] : k4_xboole_0(A_1019,A_1019) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_63886])).

tff(c_63895,plain,(
    ! [A_1019] : k4_xboole_0(A_1019,k1_xboole_0) = k3_xboole_0(A_1019,A_1019) ),
    inference(superposition,[status(thm),theory(equality)],[c_63890,c_32])).

tff(c_63913,plain,(
    ! [A_1019] : k3_xboole_0(A_1019,A_1019) = A_1019 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_63895])).

tff(c_64507,plain,(
    ! [A_1060,B_1061,C_1062] : k4_xboole_0(k3_xboole_0(A_1060,B_1061),C_1062) = k3_xboole_0(A_1060,k4_xboole_0(B_1061,C_1062)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65229,plain,(
    ! [A_1095,C_1096] : k3_xboole_0(A_1095,k4_xboole_0(A_1095,C_1096)) = k4_xboole_0(A_1095,C_1096) ),
    inference(superposition,[status(thm),theory(equality)],[c_63913,c_64507])).

tff(c_65284,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k3_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_65229])).

tff(c_65482,plain,(
    ! [A_1106,B_1107] : k3_xboole_0(A_1106,k3_xboole_0(A_1106,B_1107)) = k3_xboole_0(A_1106,B_1107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_65284])).

tff(c_65516,plain,(
    ! [A_1106,B_1107] : k5_xboole_0(A_1106,k3_xboole_0(A_1106,B_1107)) = k4_xboole_0(A_1106,k3_xboole_0(A_1106,B_1107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65482,c_26])).

tff(c_65554,plain,(
    ! [A_1106,B_1107] : k4_xboole_0(A_1106,k3_xboole_0(A_1106,B_1107)) = k4_xboole_0(A_1106,B_1107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_65516])).

tff(c_142443,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_142194,c_65554])).

tff(c_142528,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_142443])).

tff(c_38,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_143071,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_142528,c_38])).

tff(c_143169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63857,c_143071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:30:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.66/17.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.66/17.14  
% 26.66/17.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.66/17.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 26.66/17.15  
% 26.66/17.15  %Foreground sorts:
% 26.66/17.15  
% 26.66/17.15  
% 26.66/17.15  %Background operators:
% 26.66/17.15  
% 26.66/17.15  
% 26.66/17.15  %Foreground operators:
% 26.66/17.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.66/17.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.66/17.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.66/17.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.66/17.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 26.66/17.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.66/17.15  tff('#skF_5', type, '#skF_5': $i).
% 26.66/17.15  tff('#skF_6', type, '#skF_6': $i).
% 26.66/17.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.66/17.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.66/17.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.66/17.15  tff('#skF_4', type, '#skF_4': $i).
% 26.66/17.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 26.66/17.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.66/17.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.66/17.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.66/17.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 26.66/17.15  
% 26.66/17.16  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 26.66/17.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 26.66/17.16  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 26.66/17.16  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 26.66/17.16  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 26.66/17.16  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 26.66/17.16  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 26.66/17.16  tff(f_52, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 26.66/17.16  tff(f_56, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 26.66/17.16  tff(c_44, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.66/17.16  tff(c_68, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 26.66/17.16  tff(c_46, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.66/17.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.66/17.16  tff(c_264, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.66/17.16  tff(c_4758, plain, (![A_213, B_214, B_215]: (r2_hidden('#skF_1'(A_213, B_214), B_215) | ~r1_tarski(A_213, B_215) | r1_tarski(A_213, B_214))), inference(resolution, [status(thm)], [c_6, c_264])).
% 26.66/17.16  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 26.66/17.16  tff(c_63748, plain, (![A_1005, B_1006, A_1007, B_1008]: (r2_hidden('#skF_1'(A_1005, B_1006), A_1007) | ~r1_tarski(A_1005, k4_xboole_0(A_1007, B_1008)) | r1_tarski(A_1005, B_1006))), inference(resolution, [status(thm)], [c_4758, c_12])).
% 26.66/17.16  tff(c_63841, plain, (![B_1009]: (r2_hidden('#skF_1'('#skF_4', B_1009), '#skF_5') | r1_tarski('#skF_4', B_1009))), inference(resolution, [status(thm)], [c_46, c_63748])).
% 26.66/17.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.66/17.16  tff(c_63850, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_63841, c_4])).
% 26.66/17.16  tff(c_63856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_63850])).
% 26.66/17.16  tff(c_63857, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 26.66/17.16  tff(c_30, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_48])).
% 26.66/17.16  tff(c_32, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 26.66/17.16  tff(c_64011, plain, (![A_1033, B_1034]: (r2_hidden('#skF_1'(A_1033, B_1034), A_1033) | r1_tarski(A_1033, B_1034))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.66/17.16  tff(c_72832, plain, (![A_1254, B_1255, B_1256]: (r2_hidden('#skF_1'(k4_xboole_0(A_1254, B_1255), B_1256), A_1254) | r1_tarski(k4_xboole_0(A_1254, B_1255), B_1256))), inference(resolution, [status(thm)], [c_64011, c_12])).
% 26.66/17.16  tff(c_72943, plain, (![A_1257, B_1258]: (r1_tarski(k4_xboole_0(A_1257, B_1258), A_1257))), inference(resolution, [status(thm)], [c_72832, c_4])).
% 26.66/17.16  tff(c_72970, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_72943])).
% 26.66/17.16  tff(c_64679, plain, (![D_1069, A_1070, B_1071]: (r2_hidden(D_1069, k4_xboole_0(A_1070, B_1071)) | r2_hidden(D_1069, B_1071) | ~r2_hidden(D_1069, A_1070))), inference(cnfTransformation, [status(thm)], [f_42])).
% 26.66/17.16  tff(c_93930, plain, (![A_1500, A_1501, B_1502]: (r1_tarski(A_1500, k4_xboole_0(A_1501, B_1502)) | r2_hidden('#skF_1'(A_1500, k4_xboole_0(A_1501, B_1502)), B_1502) | ~r2_hidden('#skF_1'(A_1500, k4_xboole_0(A_1501, B_1502)), A_1501))), inference(resolution, [status(thm)], [c_64679, c_4])).
% 26.66/17.16  tff(c_94006, plain, (![A_1, B_1502]: (r2_hidden('#skF_1'(A_1, k4_xboole_0(A_1, B_1502)), B_1502) | r1_tarski(A_1, k4_xboole_0(A_1, B_1502)))), inference(resolution, [status(thm)], [c_6, c_93930])).
% 26.66/17.16  tff(c_64048, plain, (![C_1039, B_1040, A_1041]: (r2_hidden(C_1039, B_1040) | ~r2_hidden(C_1039, A_1041) | ~r1_tarski(A_1041, B_1040))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.66/17.16  tff(c_68373, plain, (![A_1187, B_1188, B_1189]: (r2_hidden('#skF_1'(A_1187, B_1188), B_1189) | ~r1_tarski(A_1187, B_1189) | r1_tarski(A_1187, B_1188))), inference(resolution, [status(thm)], [c_6, c_64048])).
% 26.66/17.16  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 26.66/17.16  tff(c_119927, plain, (![A_1933, B_1934, B_1935, A_1936]: (~r2_hidden('#skF_1'(A_1933, B_1934), B_1935) | ~r1_tarski(A_1933, k4_xboole_0(A_1936, B_1935)) | r1_tarski(A_1933, B_1934))), inference(resolution, [status(thm)], [c_68373, c_10])).
% 26.66/17.16  tff(c_135160, plain, (![A_2101, A_2102, B_2103]: (~r1_tarski(A_2101, k4_xboole_0(A_2102, B_2103)) | r1_tarski(A_2101, k4_xboole_0(A_2101, B_2103)))), inference(resolution, [status(thm)], [c_94006, c_119927])).
% 26.66/17.16  tff(c_135256, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_135160])).
% 26.66/17.16  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.66/17.16  tff(c_68408, plain, (![A_1187, B_1188, B_2, B_1189]: (r2_hidden('#skF_1'(A_1187, B_1188), B_2) | ~r1_tarski(B_1189, B_2) | ~r1_tarski(A_1187, B_1189) | r1_tarski(A_1187, B_1188))), inference(resolution, [status(thm)], [c_68373, c_2])).
% 26.66/17.16  tff(c_142090, plain, (![A_2138, B_2139]: (r2_hidden('#skF_1'(A_2138, B_2139), k4_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski(A_2138, '#skF_4') | r1_tarski(A_2138, B_2139))), inference(resolution, [status(thm)], [c_135256, c_68408])).
% 26.66/17.16  tff(c_68772, plain, (![A_1202, B_1203, B_1204]: (~r2_hidden('#skF_1'(k4_xboole_0(A_1202, B_1203), B_1204), B_1203) | r1_tarski(k4_xboole_0(A_1202, B_1203), B_1204))), inference(resolution, [status(thm)], [c_64011, c_10])).
% 26.66/17.16  tff(c_68801, plain, (![A_16, B_17, B_1204]: (~r2_hidden('#skF_1'(k3_xboole_0(A_16, B_17), B_1204), k4_xboole_0(A_16, B_17)) | r1_tarski(k4_xboole_0(A_16, k4_xboole_0(A_16, B_17)), B_1204))), inference(superposition, [status(thm), theory('equality')], [c_32, c_68772])).
% 26.66/17.16  tff(c_68813, plain, (![A_16, B_17, B_1204]: (~r2_hidden('#skF_1'(k3_xboole_0(A_16, B_17), B_1204), k4_xboole_0(A_16, B_17)) | r1_tarski(k3_xboole_0(A_16, B_17), B_1204))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68801])).
% 26.66/17.16  tff(c_142094, plain, (![B_2139]: (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_4') | r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), B_2139))), inference(resolution, [status(thm)], [c_142090, c_68813])).
% 26.66/17.16  tff(c_142136, plain, (![B_2140]: (r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), B_2140))), inference(demodulation, [status(thm), theory('equality')], [c_72970, c_142094])).
% 26.66/17.16  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 26.66/17.16  tff(c_63865, plain, (![A_1017, B_1018]: (k4_xboole_0(A_1017, k4_xboole_0(A_1017, B_1018))=k3_xboole_0(A_1017, B_1018))), inference(cnfTransformation, [status(thm)], [f_50])).
% 26.66/17.16  tff(c_63886, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_63865])).
% 26.66/17.16  tff(c_63889, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_63886])).
% 26.66/17.16  tff(c_65144, plain, (![A_1090, B_1091, C_1092]: (r2_hidden('#skF_2'(A_1090, B_1091, C_1092), A_1090) | r2_hidden('#skF_3'(A_1090, B_1091, C_1092), C_1092) | k4_xboole_0(A_1090, B_1091)=C_1092)), inference(cnfTransformation, [status(thm)], [f_42])).
% 26.66/17.16  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 26.66/17.16  tff(c_65147, plain, (![A_1090, C_1092]: (r2_hidden('#skF_3'(A_1090, A_1090, C_1092), C_1092) | k4_xboole_0(A_1090, A_1090)=C_1092)), inference(resolution, [status(thm)], [c_65144, c_22])).
% 26.66/17.16  tff(c_65200, plain, (![A_1093, C_1094]: (r2_hidden('#skF_3'(A_1093, A_1093, C_1094), C_1094) | k1_xboole_0=C_1094)), inference(demodulation, [status(thm), theory('equality')], [c_63889, c_65147])).
% 26.66/17.16  tff(c_65221, plain, (![A_1093, C_1094, B_2]: (r2_hidden('#skF_3'(A_1093, A_1093, C_1094), B_2) | ~r1_tarski(C_1094, B_2) | k1_xboole_0=C_1094)), inference(resolution, [status(thm)], [c_65200, c_2])).
% 26.66/17.16  tff(c_117010, plain, (![A_1880, A_1881, B_1882]: (~r2_hidden('#skF_3'(A_1880, A_1880, k4_xboole_0(A_1881, B_1882)), B_1882) | k4_xboole_0(A_1881, B_1882)=k1_xboole_0)), inference(resolution, [status(thm)], [c_65200, c_10])).
% 26.66/17.16  tff(c_117110, plain, (![A_1880, A_15]: (~r2_hidden('#skF_3'(A_1880, A_1880, A_15), k1_xboole_0) | k4_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_117010])).
% 26.66/17.16  tff(c_117144, plain, (![A_1883, A_1884]: (~r2_hidden('#skF_3'(A_1883, A_1883, A_1884), k1_xboole_0) | k1_xboole_0=A_1884)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_117110])).
% 26.66/17.16  tff(c_117193, plain, (![C_1094]: (~r1_tarski(C_1094, k1_xboole_0) | k1_xboole_0=C_1094)), inference(resolution, [status(thm)], [c_65221, c_117144])).
% 26.66/17.16  tff(c_142194, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_142136, c_117193])).
% 26.66/17.16  tff(c_26, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 26.66/17.16  tff(c_63890, plain, (![A_1019]: (k4_xboole_0(A_1019, A_1019)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_63886])).
% 26.66/17.16  tff(c_63895, plain, (![A_1019]: (k4_xboole_0(A_1019, k1_xboole_0)=k3_xboole_0(A_1019, A_1019))), inference(superposition, [status(thm), theory('equality')], [c_63890, c_32])).
% 26.66/17.16  tff(c_63913, plain, (![A_1019]: (k3_xboole_0(A_1019, A_1019)=A_1019)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_63895])).
% 26.66/17.16  tff(c_64507, plain, (![A_1060, B_1061, C_1062]: (k4_xboole_0(k3_xboole_0(A_1060, B_1061), C_1062)=k3_xboole_0(A_1060, k4_xboole_0(B_1061, C_1062)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 26.66/17.16  tff(c_65229, plain, (![A_1095, C_1096]: (k3_xboole_0(A_1095, k4_xboole_0(A_1095, C_1096))=k4_xboole_0(A_1095, C_1096))), inference(superposition, [status(thm), theory('equality')], [c_63913, c_64507])).
% 26.66/17.16  tff(c_65284, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k3_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_65229])).
% 26.66/17.16  tff(c_65482, plain, (![A_1106, B_1107]: (k3_xboole_0(A_1106, k3_xboole_0(A_1106, B_1107))=k3_xboole_0(A_1106, B_1107))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_65284])).
% 26.66/17.16  tff(c_65516, plain, (![A_1106, B_1107]: (k5_xboole_0(A_1106, k3_xboole_0(A_1106, B_1107))=k4_xboole_0(A_1106, k3_xboole_0(A_1106, B_1107)))), inference(superposition, [status(thm), theory('equality')], [c_65482, c_26])).
% 26.66/17.16  tff(c_65554, plain, (![A_1106, B_1107]: (k4_xboole_0(A_1106, k3_xboole_0(A_1106, B_1107))=k4_xboole_0(A_1106, B_1107))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_65516])).
% 26.66/17.16  tff(c_142443, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_142194, c_65554])).
% 26.66/17.16  tff(c_142528, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_142443])).
% 26.66/17.16  tff(c_38, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 26.66/17.16  tff(c_143071, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_142528, c_38])).
% 26.66/17.16  tff(c_143169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63857, c_143071])).
% 26.66/17.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.66/17.16  
% 26.66/17.16  Inference rules
% 26.66/17.16  ----------------------
% 26.66/17.16  #Ref     : 0
% 26.66/17.16  #Sup     : 35973
% 26.66/17.16  #Fact    : 0
% 26.66/17.16  #Define  : 0
% 26.66/17.16  #Split   : 10
% 26.66/17.16  #Chain   : 0
% 26.66/17.16  #Close   : 0
% 26.66/17.16  
% 26.66/17.16  Ordering : KBO
% 26.66/17.16  
% 26.66/17.16  Simplification rules
% 26.66/17.16  ----------------------
% 26.66/17.16  #Subsume      : 3884
% 26.66/17.16  #Demod        : 48826
% 26.66/17.16  #Tautology    : 21001
% 26.66/17.16  #SimpNegUnit  : 13
% 26.66/17.16  #BackRed      : 141
% 26.66/17.16  
% 26.66/17.16  #Partial instantiations: 0
% 26.66/17.16  #Strategies tried      : 1
% 26.66/17.16  
% 26.66/17.16  Timing (in seconds)
% 26.66/17.16  ----------------------
% 26.66/17.17  Preprocessing        : 0.31
% 26.66/17.17  Parsing              : 0.16
% 26.66/17.17  CNF conversion       : 0.02
% 26.66/17.17  Main loop            : 16.09
% 26.66/17.17  Inferencing          : 2.28
% 26.66/17.17  Reduction            : 9.42
% 26.66/17.17  Demodulation         : 8.46
% 26.66/17.17  BG Simplification    : 0.28
% 26.66/17.17  Subsumption          : 3.31
% 26.66/17.17  Abstraction          : 0.51
% 26.66/17.17  MUC search           : 0.00
% 26.66/17.17  Cooper               : 0.00
% 26.66/17.17  Total                : 16.44
% 26.66/17.17  Index Insertion      : 0.00
% 26.66/17.17  Index Deletion       : 0.00
% 26.66/17.17  Index Matching       : 0.00
% 26.66/17.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
