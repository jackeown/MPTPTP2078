%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:18 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 348 expanded)
%              Number of leaves         :   27 ( 126 expanded)
%              Depth                    :   15
%              Number of atoms          :  125 ( 794 expanded)
%              Number of equality atoms :   23 ( 125 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_12,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1760,plain,(
    ! [C_175,A_176,D_177] :
      ( r2_hidden(C_175,k1_relat_1(A_176))
      | ~ r2_hidden(k4_tarski(C_175,D_177),A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1766,plain,(
    ! [C_178,D_179] : r2_hidden(C_178,k1_relat_1(k1_tarski(k4_tarski(C_178,D_179)))) ),
    inference(resolution,[status(thm)],[c_12,c_1760])).

tff(c_26,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k1_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(C_28,D_31),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1771,plain,(
    ! [C_28,D_31,D_179] : r2_hidden(C_28,k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(C_28,D_31),D_179))))) ),
    inference(resolution,[status(thm)],[c_1766,c_26])).

tff(c_2200,plain,(
    ! [A_233,B_234] :
      ( r2_hidden(k4_tarski('#skF_4'(A_233,B_234),'#skF_5'(A_233,B_234)),A_233)
      | r2_hidden('#skF_6'(A_233,B_234),B_234)
      | k1_relat_1(A_233) = B_234 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2763,plain,(
    ! [A_278,B_279] :
      ( r2_hidden('#skF_4'(A_278,B_279),k1_relat_1(A_278))
      | r2_hidden('#skF_6'(A_278,B_279),B_279)
      | k1_relat_1(A_278) = B_279 ) ),
    inference(resolution,[status(thm)],[c_2200,c_26])).

tff(c_24,plain,(
    ! [C_28,A_13] :
      ( r2_hidden(k4_tarski(C_28,'#skF_7'(A_13,k1_relat_1(A_13),C_28)),A_13)
      | ~ r2_hidden(C_28,k1_relat_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2020,plain,(
    ! [C_221,A_222] :
      ( r2_hidden(k4_tarski(C_221,'#skF_7'(A_222,k1_relat_1(A_222),C_221)),A_222)
      | ~ r2_hidden(C_221,k1_relat_1(A_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1772,plain,(
    ! [A_180,B_181,C_182] :
      ( ~ r1_xboole_0(A_180,B_181)
      | ~ r2_hidden(C_182,B_181)
      | ~ r2_hidden(C_182,A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1775,plain,(
    ! [C_182,A_6] :
      ( ~ r2_hidden(C_182,k1_xboole_0)
      | ~ r2_hidden(C_182,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_1772])).

tff(c_2560,plain,(
    ! [C_266,A_267] :
      ( ~ r2_hidden(k4_tarski(C_266,'#skF_7'(k1_xboole_0,k1_relat_1(k1_xboole_0),C_266)),A_267)
      | ~ r2_hidden(C_266,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_2020,c_1775])).

tff(c_2591,plain,(
    ! [C_28] : ~ r2_hidden(C_28,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_24,c_2560])).

tff(c_2992,plain,(
    ! [B_288] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_288),B_288)
      | k1_relat_1(k1_xboole_0) = B_288 ) ),
    inference(resolution,[status(thm)],[c_2763,c_2591])).

tff(c_3051,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_6'(k1_xboole_0,k1_xboole_0),A_6)
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2992,c_1775])).

tff(c_3144,plain,(
    ! [A_292] : ~ r2_hidden('#skF_6'(k1_xboole_0,k1_xboole_0),A_292) ),
    inference(splitLeft,[status(thm)],[c_3051])).

tff(c_3182,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1771,c_3144])).

tff(c_3183,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3051])).

tff(c_3188,plain,(
    ! [C_28] : ~ r2_hidden(C_28,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3183,c_2591])).

tff(c_42,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_67,plain,(
    k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_48])).

tff(c_115,plain,(
    ! [C_52,A_53,D_54] :
      ( r2_hidden(C_52,k1_relat_1(A_53))
      | ~ r2_hidden(k4_tarski(C_52,D_54),A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_122,plain,(
    ! [C_55,D_56] : r2_hidden(C_55,k1_relat_1(k1_tarski(k4_tarski(C_55,D_56)))) ),
    inference(resolution,[status(thm)],[c_12,c_115])).

tff(c_127,plain,(
    ! [C_28,D_31,D_56] : r2_hidden(C_28,k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(C_28,D_31),D_56))))) ),
    inference(resolution,[status(thm)],[c_122,c_26])).

tff(c_834,plain,(
    ! [A_126,B_127] :
      ( r2_hidden(k4_tarski('#skF_4'(A_126,B_127),'#skF_5'(A_126,B_127)),A_126)
      | r2_hidden('#skF_6'(A_126,B_127),B_127)
      | k1_relat_1(A_126) = B_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden(k4_tarski(A_71,B_72),C_73)
      | ~ r2_hidden(B_72,k11_relat_1(C_73,A_71))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_188,plain,(
    ! [A_76,C_77,B_78] :
      ( r2_hidden(A_76,k1_relat_1(C_77))
      | ~ r2_hidden(B_78,k11_relat_1(C_77,A_76))
      | ~ v1_relat_1(C_77) ) ),
    inference(resolution,[status(thm)],[c_169,c_26])).

tff(c_205,plain,(
    ! [A_79,C_80,A_81] :
      ( r2_hidden(A_79,k1_relat_1(C_80))
      | ~ v1_relat_1(C_80)
      | r1_xboole_0(A_81,k11_relat_1(C_80,A_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_220,plain,(
    ! [A_81] :
      ( ~ v1_relat_1('#skF_9')
      | r1_xboole_0(A_81,k11_relat_1('#skF_9','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_205,c_66])).

tff(c_230,plain,(
    ! [A_82] : r1_xboole_0(A_82,k11_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_220])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_233,plain,(
    ! [C_5,A_82] :
      ( ~ r2_hidden(C_5,k11_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(C_5,A_82) ) ),
    inference(resolution,[status(thm)],[c_230,c_2])).

tff(c_1281,plain,(
    ! [B_159,A_160] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(k11_relat_1('#skF_9','#skF_8'),B_159),'#skF_5'(k11_relat_1('#skF_9','#skF_8'),B_159)),A_160)
      | r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),B_159),B_159)
      | k1_relat_1(k11_relat_1('#skF_9','#skF_8')) = B_159 ) ),
    inference(resolution,[status(thm)],[c_834,c_233])).

tff(c_1321,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),B_161),B_161)
      | k1_relat_1(k11_relat_1('#skF_9','#skF_8')) = B_161 ) ),
    inference(resolution,[status(thm)],[c_127,c_1281])).

tff(c_1387,plain,(
    ! [A_82] :
      ( ~ r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),k11_relat_1('#skF_9','#skF_8')),A_82)
      | k1_relat_1(k11_relat_1('#skF_9','#skF_8')) = k11_relat_1('#skF_9','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1321,c_233])).

tff(c_1487,plain,(
    ! [A_165] : ~ r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),k11_relat_1('#skF_9','#skF_8')),A_165) ),
    inference(splitLeft,[status(thm)],[c_1387])).

tff(c_1523,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_127,c_1487])).

tff(c_1524,plain,(
    k1_relat_1(k11_relat_1('#skF_9','#skF_8')) = k11_relat_1('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1387])).

tff(c_1316,plain,(
    ! [B_159] :
      ( r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),B_159),B_159)
      | k1_relat_1(k11_relat_1('#skF_9','#skF_8')) = B_159 ) ),
    inference(resolution,[status(thm)],[c_127,c_1281])).

tff(c_1526,plain,(
    ! [B_159] :
      ( r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),B_159),B_159)
      | k11_relat_1('#skF_9','#skF_8') = B_159 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_1316])).

tff(c_1609,plain,(
    ! [B_167] :
      ( r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),B_167),B_167)
      | k11_relat_1('#skF_9','#skF_8') = B_167 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_1316])).

tff(c_80,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [C_46,A_6] :
      ( ~ r2_hidden(C_46,k1_xboole_0)
      | ~ r2_hidden(C_46,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_1636,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),k1_xboole_0),A_6)
      | k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1609,c_83])).

tff(c_1704,plain,(
    ! [A_170] : ~ r2_hidden('#skF_6'(k11_relat_1('#skF_9','#skF_8'),k1_xboole_0),A_170) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1636])).

tff(c_1710,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1526,c_1704])).

tff(c_1739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1710])).

tff(c_1741,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1740,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_38,plain,(
    ! [B_33,C_34,A_32] :
      ( r2_hidden(B_33,k11_relat_1(C_34,A_32))
      | ~ r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3295,plain,(
    ! [A_295,C_296] :
      ( r2_hidden('#skF_7'(A_295,k1_relat_1(A_295),C_296),k11_relat_1(A_295,C_296))
      | ~ v1_relat_1(A_295)
      | ~ r2_hidden(C_296,k1_relat_1(A_295)) ) ),
    inference(resolution,[status(thm)],[c_2020,c_38])).

tff(c_3309,plain,
    ( r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1740,c_3295])).

tff(c_3315,plain,(
    r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_40,c_3309])).

tff(c_3317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3188,c_3315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.86  
% 4.32/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.86  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.32/1.86  
% 4.32/1.86  %Foreground sorts:
% 4.32/1.86  
% 4.32/1.86  
% 4.32/1.86  %Background operators:
% 4.32/1.86  
% 4.32/1.86  
% 4.32/1.86  %Foreground operators:
% 4.32/1.86  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.32/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.32/1.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.32/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.32/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.32/1.86  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.32/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.32/1.86  tff('#skF_9', type, '#skF_9': $i).
% 4.32/1.86  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.32/1.86  tff('#skF_8', type, '#skF_8': $i).
% 4.32/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.32/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.32/1.86  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.32/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/1.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.32/1.86  
% 4.32/1.88  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.32/1.88  tff(f_62, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.32/1.88  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.32/1.88  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.32/1.88  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.32/1.88  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.32/1.88  tff(c_12, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.32/1.88  tff(c_1760, plain, (![C_175, A_176, D_177]: (r2_hidden(C_175, k1_relat_1(A_176)) | ~r2_hidden(k4_tarski(C_175, D_177), A_176))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.32/1.88  tff(c_1766, plain, (![C_178, D_179]: (r2_hidden(C_178, k1_relat_1(k1_tarski(k4_tarski(C_178, D_179)))))), inference(resolution, [status(thm)], [c_12, c_1760])).
% 4.32/1.88  tff(c_26, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k1_relat_1(A_13)) | ~r2_hidden(k4_tarski(C_28, D_31), A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.32/1.88  tff(c_1771, plain, (![C_28, D_31, D_179]: (r2_hidden(C_28, k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(C_28, D_31), D_179))))))), inference(resolution, [status(thm)], [c_1766, c_26])).
% 4.32/1.88  tff(c_2200, plain, (![A_233, B_234]: (r2_hidden(k4_tarski('#skF_4'(A_233, B_234), '#skF_5'(A_233, B_234)), A_233) | r2_hidden('#skF_6'(A_233, B_234), B_234) | k1_relat_1(A_233)=B_234)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.32/1.88  tff(c_2763, plain, (![A_278, B_279]: (r2_hidden('#skF_4'(A_278, B_279), k1_relat_1(A_278)) | r2_hidden('#skF_6'(A_278, B_279), B_279) | k1_relat_1(A_278)=B_279)), inference(resolution, [status(thm)], [c_2200, c_26])).
% 4.32/1.88  tff(c_24, plain, (![C_28, A_13]: (r2_hidden(k4_tarski(C_28, '#skF_7'(A_13, k1_relat_1(A_13), C_28)), A_13) | ~r2_hidden(C_28, k1_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.32/1.88  tff(c_2020, plain, (![C_221, A_222]: (r2_hidden(k4_tarski(C_221, '#skF_7'(A_222, k1_relat_1(A_222), C_221)), A_222) | ~r2_hidden(C_221, k1_relat_1(A_222)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.32/1.88  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.32/1.88  tff(c_1772, plain, (![A_180, B_181, C_182]: (~r1_xboole_0(A_180, B_181) | ~r2_hidden(C_182, B_181) | ~r2_hidden(C_182, A_180))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.32/1.88  tff(c_1775, plain, (![C_182, A_6]: (~r2_hidden(C_182, k1_xboole_0) | ~r2_hidden(C_182, A_6))), inference(resolution, [status(thm)], [c_8, c_1772])).
% 4.32/1.88  tff(c_2560, plain, (![C_266, A_267]: (~r2_hidden(k4_tarski(C_266, '#skF_7'(k1_xboole_0, k1_relat_1(k1_xboole_0), C_266)), A_267) | ~r2_hidden(C_266, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2020, c_1775])).
% 4.32/1.88  tff(c_2591, plain, (![C_28]: (~r2_hidden(C_28, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_24, c_2560])).
% 4.32/1.88  tff(c_2992, plain, (![B_288]: (r2_hidden('#skF_6'(k1_xboole_0, B_288), B_288) | k1_relat_1(k1_xboole_0)=B_288)), inference(resolution, [status(thm)], [c_2763, c_2591])).
% 4.32/1.88  tff(c_3051, plain, (![A_6]: (~r2_hidden('#skF_6'(k1_xboole_0, k1_xboole_0), A_6) | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2992, c_1775])).
% 4.32/1.88  tff(c_3144, plain, (![A_292]: (~r2_hidden('#skF_6'(k1_xboole_0, k1_xboole_0), A_292))), inference(splitLeft, [status(thm)], [c_3051])).
% 4.32/1.88  tff(c_3182, plain, $false, inference(resolution, [status(thm)], [c_1771, c_3144])).
% 4.32/1.88  tff(c_3183, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3051])).
% 4.32/1.88  tff(c_3188, plain, (![C_28]: (~r2_hidden(C_28, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3183, c_2591])).
% 4.32/1.88  tff(c_42, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.32/1.88  tff(c_66, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.32/1.88  tff(c_48, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9')) | k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.32/1.88  tff(c_67, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_48])).
% 4.32/1.88  tff(c_115, plain, (![C_52, A_53, D_54]: (r2_hidden(C_52, k1_relat_1(A_53)) | ~r2_hidden(k4_tarski(C_52, D_54), A_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.32/1.88  tff(c_122, plain, (![C_55, D_56]: (r2_hidden(C_55, k1_relat_1(k1_tarski(k4_tarski(C_55, D_56)))))), inference(resolution, [status(thm)], [c_12, c_115])).
% 4.32/1.88  tff(c_127, plain, (![C_28, D_31, D_56]: (r2_hidden(C_28, k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(C_28, D_31), D_56))))))), inference(resolution, [status(thm)], [c_122, c_26])).
% 4.32/1.88  tff(c_834, plain, (![A_126, B_127]: (r2_hidden(k4_tarski('#skF_4'(A_126, B_127), '#skF_5'(A_126, B_127)), A_126) | r2_hidden('#skF_6'(A_126, B_127), B_127) | k1_relat_1(A_126)=B_127)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.32/1.88  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.32/1.88  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.32/1.88  tff(c_169, plain, (![A_71, B_72, C_73]: (r2_hidden(k4_tarski(A_71, B_72), C_73) | ~r2_hidden(B_72, k11_relat_1(C_73, A_71)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.32/1.88  tff(c_188, plain, (![A_76, C_77, B_78]: (r2_hidden(A_76, k1_relat_1(C_77)) | ~r2_hidden(B_78, k11_relat_1(C_77, A_76)) | ~v1_relat_1(C_77))), inference(resolution, [status(thm)], [c_169, c_26])).
% 4.32/1.88  tff(c_205, plain, (![A_79, C_80, A_81]: (r2_hidden(A_79, k1_relat_1(C_80)) | ~v1_relat_1(C_80) | r1_xboole_0(A_81, k11_relat_1(C_80, A_79)))), inference(resolution, [status(thm)], [c_4, c_188])).
% 4.32/1.88  tff(c_220, plain, (![A_81]: (~v1_relat_1('#skF_9') | r1_xboole_0(A_81, k11_relat_1('#skF_9', '#skF_8')))), inference(resolution, [status(thm)], [c_205, c_66])).
% 4.32/1.88  tff(c_230, plain, (![A_82]: (r1_xboole_0(A_82, k11_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_220])).
% 4.32/1.88  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.32/1.88  tff(c_233, plain, (![C_5, A_82]: (~r2_hidden(C_5, k11_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(C_5, A_82))), inference(resolution, [status(thm)], [c_230, c_2])).
% 4.32/1.88  tff(c_1281, plain, (![B_159, A_160]: (~r2_hidden(k4_tarski('#skF_4'(k11_relat_1('#skF_9', '#skF_8'), B_159), '#skF_5'(k11_relat_1('#skF_9', '#skF_8'), B_159)), A_160) | r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), B_159), B_159) | k1_relat_1(k11_relat_1('#skF_9', '#skF_8'))=B_159)), inference(resolution, [status(thm)], [c_834, c_233])).
% 4.32/1.88  tff(c_1321, plain, (![B_161]: (r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), B_161), B_161) | k1_relat_1(k11_relat_1('#skF_9', '#skF_8'))=B_161)), inference(resolution, [status(thm)], [c_127, c_1281])).
% 4.32/1.88  tff(c_1387, plain, (![A_82]: (~r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), k11_relat_1('#skF_9', '#skF_8')), A_82) | k1_relat_1(k11_relat_1('#skF_9', '#skF_8'))=k11_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_1321, c_233])).
% 4.32/1.88  tff(c_1487, plain, (![A_165]: (~r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), k11_relat_1('#skF_9', '#skF_8')), A_165))), inference(splitLeft, [status(thm)], [c_1387])).
% 4.32/1.88  tff(c_1523, plain, $false, inference(resolution, [status(thm)], [c_127, c_1487])).
% 4.32/1.88  tff(c_1524, plain, (k1_relat_1(k11_relat_1('#skF_9', '#skF_8'))=k11_relat_1('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_1387])).
% 4.32/1.88  tff(c_1316, plain, (![B_159]: (r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), B_159), B_159) | k1_relat_1(k11_relat_1('#skF_9', '#skF_8'))=B_159)), inference(resolution, [status(thm)], [c_127, c_1281])).
% 4.32/1.88  tff(c_1526, plain, (![B_159]: (r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), B_159), B_159) | k11_relat_1('#skF_9', '#skF_8')=B_159)), inference(demodulation, [status(thm), theory('equality')], [c_1524, c_1316])).
% 4.32/1.88  tff(c_1609, plain, (![B_167]: (r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), B_167), B_167) | k11_relat_1('#skF_9', '#skF_8')=B_167)), inference(demodulation, [status(thm), theory('equality')], [c_1524, c_1316])).
% 4.32/1.88  tff(c_80, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, B_45) | ~r2_hidden(C_46, A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.32/1.88  tff(c_83, plain, (![C_46, A_6]: (~r2_hidden(C_46, k1_xboole_0) | ~r2_hidden(C_46, A_6))), inference(resolution, [status(thm)], [c_8, c_80])).
% 4.32/1.88  tff(c_1636, plain, (![A_6]: (~r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), k1_xboole_0), A_6) | k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1609, c_83])).
% 4.32/1.88  tff(c_1704, plain, (![A_170]: (~r2_hidden('#skF_6'(k11_relat_1('#skF_9', '#skF_8'), k1_xboole_0), A_170))), inference(negUnitSimplification, [status(thm)], [c_67, c_1636])).
% 4.32/1.88  tff(c_1710, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_1526, c_1704])).
% 4.32/1.88  tff(c_1739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_1710])).
% 4.32/1.88  tff(c_1741, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_42])).
% 4.32/1.88  tff(c_1740, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 4.32/1.88  tff(c_38, plain, (![B_33, C_34, A_32]: (r2_hidden(B_33, k11_relat_1(C_34, A_32)) | ~r2_hidden(k4_tarski(A_32, B_33), C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.32/1.88  tff(c_3295, plain, (![A_295, C_296]: (r2_hidden('#skF_7'(A_295, k1_relat_1(A_295), C_296), k11_relat_1(A_295, C_296)) | ~v1_relat_1(A_295) | ~r2_hidden(C_296, k1_relat_1(A_295)))), inference(resolution, [status(thm)], [c_2020, c_38])).
% 4.32/1.88  tff(c_3309, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0) | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1740, c_3295])).
% 4.32/1.88  tff(c_3315, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_40, c_3309])).
% 4.32/1.88  tff(c_3317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3188, c_3315])).
% 4.32/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.88  
% 4.32/1.88  Inference rules
% 4.32/1.88  ----------------------
% 4.32/1.88  #Ref     : 0
% 4.32/1.88  #Sup     : 693
% 4.32/1.88  #Fact    : 0
% 4.32/1.88  #Define  : 0
% 4.32/1.88  #Split   : 6
% 4.32/1.88  #Chain   : 0
% 4.32/1.88  #Close   : 0
% 4.32/1.88  
% 4.32/1.88  Ordering : KBO
% 4.32/1.88  
% 4.32/1.88  Simplification rules
% 4.32/1.88  ----------------------
% 4.32/1.88  #Subsume      : 133
% 4.32/1.88  #Demod        : 217
% 4.32/1.88  #Tautology    : 158
% 4.32/1.88  #SimpNegUnit  : 16
% 4.32/1.88  #BackRed      : 32
% 4.32/1.88  
% 4.32/1.88  #Partial instantiations: 0
% 4.32/1.88  #Strategies tried      : 1
% 4.32/1.88  
% 4.32/1.88  Timing (in seconds)
% 4.32/1.88  ----------------------
% 4.32/1.88  Preprocessing        : 0.33
% 4.32/1.88  Parsing              : 0.17
% 4.32/1.88  CNF conversion       : 0.03
% 4.32/1.88  Main loop            : 0.75
% 4.32/1.88  Inferencing          : 0.27
% 4.32/1.88  Reduction            : 0.21
% 4.32/1.88  Demodulation         : 0.14
% 4.32/1.88  BG Simplification    : 0.05
% 4.32/1.88  Subsumption          : 0.15
% 4.32/1.88  Abstraction          : 0.05
% 4.32/1.88  MUC search           : 0.00
% 4.32/1.88  Cooper               : 0.00
% 4.32/1.88  Total                : 1.11
% 4.32/1.88  Index Insertion      : 0.00
% 4.32/1.88  Index Deletion       : 0.00
% 4.32/1.88  Index Matching       : 0.00
% 4.32/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
