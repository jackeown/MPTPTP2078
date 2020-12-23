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
% DateTime   : Thu Dec  3 09:53:59 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 168 expanded)
%              Number of leaves         :   29 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 300 expanded)
%              Number of equality atoms :   35 ( 114 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_45,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2260,plain,(
    ! [B_256,A_257] :
      ( r2_hidden(B_256,A_257)
      | k3_xboole_0(A_257,k1_tarski(B_256)) != k1_tarski(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2265,plain,(
    ! [B_256] : r2_hidden(B_256,k1_tarski(B_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2260])).

tff(c_1436,plain,(
    ! [B_136,A_137] :
      ( r2_hidden(B_136,A_137)
      | k3_xboole_0(A_137,k1_tarski(B_136)) != k1_tarski(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1441,plain,(
    ! [B_136] : r2_hidden(B_136,k1_tarski(B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1436])).

tff(c_32,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_115,plain,(
    ! [B_42,A_43] :
      ( r2_hidden(B_42,A_43)
      | k3_xboole_0(A_43,k1_tarski(B_42)) != k1_tarski(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    ! [B_42] : r2_hidden(B_42,k1_tarski(B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_115])).

tff(c_38,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_253,plain,(
    ! [A_65,C_66,B_67,D_68] :
      ( r2_hidden(A_65,C_66)
      | ~ r2_hidden(k4_tarski(A_65,B_67),k2_zfmisc_1(C_66,D_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_257,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_78,c_253])).

tff(c_304,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(k1_tarski(A_71),B_72) = k1_tarski(A_71)
      | k4_xboole_0(k1_tarski(A_71),B_72) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_39,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_430,plain,(
    ! [A_78,B_79] :
      ( r1_xboole_0(k1_tarski(A_78),B_79)
      | k4_xboole_0(k1_tarski(A_78),B_79) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_39])).

tff(c_4,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_825,plain,(
    ! [C_105,B_106,A_107] :
      ( ~ r2_hidden(C_105,B_106)
      | ~ r2_hidden(C_105,k1_tarski(A_107))
      | k4_xboole_0(k1_tarski(A_107),B_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_430,c_4])).

tff(c_1229,plain,(
    ! [A_117] :
      ( ~ r2_hidden('#skF_6',k1_tarski(A_117))
      | k4_xboole_0(k1_tarski(A_117),k1_tarski('#skF_8')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_257,c_825])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | k4_xboole_0(k1_tarski(A_20),k1_tarski(B_21)) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1305,plain,(
    ! [A_118] :
      ( A_118 = '#skF_8'
      | ~ r2_hidden('#skF_6',k1_tarski(A_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_24])).

tff(c_1312,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_120,c_1305])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1312])).

tff(c_1320,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1407,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1320,c_36])).

tff(c_1672,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( r2_hidden(k4_tarski(A_164,B_165),k2_zfmisc_1(C_166,D_167))
      | ~ r2_hidden(B_165,D_167)
      | ~ r2_hidden(A_164,C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1319,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1665,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_34])).

tff(c_1666,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1320,c_1665])).

tff(c_1675,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1672,c_1666])).

tff(c_1688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_1407,c_1675])).

tff(c_1690,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1900,plain,(
    ! [B_207,A_208] :
      ( r2_hidden(B_207,A_208)
      | k3_xboole_0(A_208,k1_tarski(B_207)) != k1_tarski(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1905,plain,(
    ! [B_207] : r2_hidden(B_207,k1_tarski(B_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1900])).

tff(c_1689,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1695,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1689])).

tff(c_1794,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_38])).

tff(c_1795,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1794])).

tff(c_1843,plain,(
    ! [B_195,D_196,A_197,C_198] :
      ( r2_hidden(B_195,D_196)
      | ~ r2_hidden(k4_tarski(A_197,B_195),k2_zfmisc_1(C_198,D_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1846,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_1795,c_1843])).

tff(c_1850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1695,c_1846])).

tff(c_1852,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1794])).

tff(c_1870,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_36])).

tff(c_1871,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1852,c_1870])).

tff(c_2137,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( r2_hidden(k4_tarski(A_235,B_236),k2_zfmisc_1(C_237,D_238))
      | ~ r2_hidden(B_236,D_238)
      | ~ r2_hidden(A_235,C_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1851,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1794])).

tff(c_2130,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1851,c_34])).

tff(c_2131,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1852,c_2130])).

tff(c_2140,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2137,c_2131])).

tff(c_2153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_1871,c_2140])).

tff(c_2155,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1689])).

tff(c_30,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2161,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_2155,c_30])).

tff(c_2520,plain,(
    ! [A_290,B_291,C_292,D_293] :
      ( r2_hidden(k4_tarski(A_290,B_291),k2_zfmisc_1(C_292,D_293))
      | ~ r2_hidden(B_291,D_293)
      | ~ r2_hidden(A_290,C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2154,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1689])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2334,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_2155,c_2154,c_28])).

tff(c_2526,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2520,c_2334])).

tff(c_2534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_2161,c_2526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.68  
% 3.70/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.68  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 3.70/1.68  
% 3.70/1.68  %Foreground sorts:
% 3.70/1.68  
% 3.70/1.68  
% 3.70/1.68  %Background operators:
% 3.70/1.68  
% 3.70/1.68  
% 3.70/1.68  %Foreground operators:
% 3.70/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.70/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.70/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.70/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.70/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.68  tff('#skF_9', type, '#skF_9': $i).
% 3.70/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.70/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.68  
% 4.04/1.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.04/1.69  tff(f_55, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 4.04/1.69  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 4.04/1.69  tff(f_61, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.04/1.69  tff(f_69, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 4.04/1.69  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.04/1.69  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 4.04/1.69  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.04/1.69  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 4.04/1.69  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.69  tff(c_2260, plain, (![B_256, A_257]: (r2_hidden(B_256, A_257) | k3_xboole_0(A_257, k1_tarski(B_256))!=k1_tarski(B_256))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.04/1.69  tff(c_2265, plain, (![B_256]: (r2_hidden(B_256, k1_tarski(B_256)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2260])).
% 4.04/1.69  tff(c_1436, plain, (![B_136, A_137]: (r2_hidden(B_136, A_137) | k3_xboole_0(A_137, k1_tarski(B_136))!=k1_tarski(B_136))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.04/1.69  tff(c_1441, plain, (![B_136]: (r2_hidden(B_136, k1_tarski(B_136)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1436])).
% 4.04/1.69  tff(c_32, plain, ('#skF_2'='#skF_4' | ~r2_hidden('#skF_7', '#skF_9') | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.04/1.69  tff(c_50, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_32])).
% 4.04/1.69  tff(c_115, plain, (![B_42, A_43]: (r2_hidden(B_42, A_43) | k3_xboole_0(A_43, k1_tarski(B_42))!=k1_tarski(B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.04/1.69  tff(c_120, plain, (![B_42]: (r2_hidden(B_42, k1_tarski(B_42)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_115])).
% 4.04/1.69  tff(c_38, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.04/1.69  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_38])).
% 4.04/1.69  tff(c_253, plain, (![A_65, C_66, B_67, D_68]: (r2_hidden(A_65, C_66) | ~r2_hidden(k4_tarski(A_65, B_67), k2_zfmisc_1(C_66, D_68)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.04/1.69  tff(c_257, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_253])).
% 4.04/1.69  tff(c_304, plain, (![A_71, B_72]: (k4_xboole_0(k1_tarski(A_71), B_72)=k1_tarski(A_71) | k4_xboole_0(k1_tarski(A_71), B_72)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.04/1.69  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.04/1.69  tff(c_14, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, k3_xboole_0(A_12, B_13)), B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.04/1.69  tff(c_39, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 4.04/1.69  tff(c_430, plain, (![A_78, B_79]: (r1_xboole_0(k1_tarski(A_78), B_79) | k4_xboole_0(k1_tarski(A_78), B_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_304, c_39])).
% 4.04/1.69  tff(c_4, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/1.69  tff(c_825, plain, (![C_105, B_106, A_107]: (~r2_hidden(C_105, B_106) | ~r2_hidden(C_105, k1_tarski(A_107)) | k4_xboole_0(k1_tarski(A_107), B_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_430, c_4])).
% 4.04/1.69  tff(c_1229, plain, (![A_117]: (~r2_hidden('#skF_6', k1_tarski(A_117)) | k4_xboole_0(k1_tarski(A_117), k1_tarski('#skF_8'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_257, c_825])).
% 4.04/1.69  tff(c_24, plain, (![B_21, A_20]: (B_21=A_20 | k4_xboole_0(k1_tarski(A_20), k1_tarski(B_21))!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.04/1.69  tff(c_1305, plain, (![A_118]: (A_118='#skF_8' | ~r2_hidden('#skF_6', k1_tarski(A_118)))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_24])).
% 4.04/1.69  tff(c_1312, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_120, c_1305])).
% 4.04/1.69  tff(c_1318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1312])).
% 4.04/1.69  tff(c_1320, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_38])).
% 4.04/1.69  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.04/1.69  tff(c_1407, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1320, c_36])).
% 4.04/1.69  tff(c_1672, plain, (![A_164, B_165, C_166, D_167]: (r2_hidden(k4_tarski(A_164, B_165), k2_zfmisc_1(C_166, D_167)) | ~r2_hidden(B_165, D_167) | ~r2_hidden(A_164, C_166))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.04/1.69  tff(c_1319, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 4.04/1.69  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.04/1.69  tff(c_1665, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_34])).
% 4.04/1.69  tff(c_1666, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1320, c_1665])).
% 4.04/1.69  tff(c_1675, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_1672, c_1666])).
% 4.04/1.69  tff(c_1688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1441, c_1407, c_1675])).
% 4.04/1.69  tff(c_1690, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_32])).
% 4.04/1.69  tff(c_1900, plain, (![B_207, A_208]: (r2_hidden(B_207, A_208) | k3_xboole_0(A_208, k1_tarski(B_207))!=k1_tarski(B_207))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.04/1.69  tff(c_1905, plain, (![B_207]: (r2_hidden(B_207, k1_tarski(B_207)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1900])).
% 4.04/1.69  tff(c_1689, plain, (~r2_hidden('#skF_7', '#skF_9') | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 4.04/1.69  tff(c_1695, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_1689])).
% 4.04/1.69  tff(c_1794, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_38])).
% 4.04/1.69  tff(c_1795, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_1794])).
% 4.04/1.69  tff(c_1843, plain, (![B_195, D_196, A_197, C_198]: (r2_hidden(B_195, D_196) | ~r2_hidden(k4_tarski(A_197, B_195), k2_zfmisc_1(C_198, D_196)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.04/1.69  tff(c_1846, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_1795, c_1843])).
% 4.04/1.69  tff(c_1850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1695, c_1846])).
% 4.04/1.69  tff(c_1852, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_1794])).
% 4.04/1.69  tff(c_1870, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_36])).
% 4.04/1.69  tff(c_1871, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1852, c_1870])).
% 4.04/1.69  tff(c_2137, plain, (![A_235, B_236, C_237, D_238]: (r2_hidden(k4_tarski(A_235, B_236), k2_zfmisc_1(C_237, D_238)) | ~r2_hidden(B_236, D_238) | ~r2_hidden(A_235, C_237))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.04/1.69  tff(c_1851, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_1794])).
% 4.04/1.69  tff(c_2130, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1851, c_34])).
% 4.04/1.69  tff(c_2131, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1852, c_2130])).
% 4.04/1.69  tff(c_2140, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_2137, c_2131])).
% 4.04/1.69  tff(c_2153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1905, c_1871, c_2140])).
% 4.04/1.69  tff(c_2155, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_1689])).
% 4.04/1.69  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_9') | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.04/1.69  tff(c_2161, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_2155, c_30])).
% 4.04/1.69  tff(c_2520, plain, (![A_290, B_291, C_292, D_293]: (r2_hidden(k4_tarski(A_290, B_291), k2_zfmisc_1(C_292, D_293)) | ~r2_hidden(B_291, D_293) | ~r2_hidden(A_290, C_292))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.04/1.69  tff(c_2154, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_1689])).
% 4.04/1.69  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | ~r2_hidden('#skF_7', '#skF_9') | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.04/1.69  tff(c_2334, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_2155, c_2154, c_28])).
% 4.04/1.69  tff(c_2526, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_2520, c_2334])).
% 4.04/1.69  tff(c_2534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2265, c_2161, c_2526])).
% 4.04/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  Inference rules
% 4.04/1.69  ----------------------
% 4.04/1.69  #Ref     : 0
% 4.04/1.69  #Sup     : 598
% 4.04/1.69  #Fact    : 6
% 4.04/1.69  #Define  : 0
% 4.04/1.69  #Split   : 8
% 4.04/1.69  #Chain   : 0
% 4.04/1.70  #Close   : 0
% 4.04/1.70  
% 4.04/1.70  Ordering : KBO
% 4.04/1.70  
% 4.04/1.70  Simplification rules
% 4.04/1.70  ----------------------
% 4.04/1.70  #Subsume      : 108
% 4.04/1.70  #Demod        : 328
% 4.04/1.70  #Tautology    : 216
% 4.04/1.70  #SimpNegUnit  : 22
% 4.04/1.70  #BackRed      : 12
% 4.04/1.70  
% 4.04/1.70  #Partial instantiations: 0
% 4.04/1.70  #Strategies tried      : 1
% 4.04/1.70  
% 4.04/1.70  Timing (in seconds)
% 4.04/1.70  ----------------------
% 4.04/1.70  Preprocessing        : 0.29
% 4.04/1.70  Parsing              : 0.15
% 4.04/1.70  CNF conversion       : 0.02
% 4.04/1.70  Main loop            : 0.62
% 4.04/1.70  Inferencing          : 0.23
% 4.04/1.70  Reduction            : 0.21
% 4.04/1.70  Demodulation         : 0.15
% 4.04/1.70  BG Simplification    : 0.03
% 4.04/1.70  Subsumption          : 0.11
% 4.04/1.70  Abstraction          : 0.03
% 4.04/1.70  MUC search           : 0.00
% 4.04/1.70  Cooper               : 0.00
% 4.04/1.70  Total                : 0.95
% 4.04/1.70  Index Insertion      : 0.00
% 4.04/1.70  Index Deletion       : 0.00
% 4.04/1.70  Index Matching       : 0.00
% 4.04/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
