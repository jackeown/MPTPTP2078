%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:38 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 236 expanded)
%              Number of leaves         :   18 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 670 expanded)
%              Number of equality atoms :    1 (   7 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_52,axiom,(
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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_34,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_106,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    ! [D_31,B_32,A_33] :
      ( r2_hidden(D_31,B_32)
      | r2_hidden(D_31,A_33)
      | ~ r2_hidden(D_31,k2_xboole_0(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_169,plain,(
    ! [A_43,B_44,B_45] :
      ( r2_hidden('#skF_3'(k2_xboole_0(A_43,B_44),B_45),B_44)
      | r2_hidden('#skF_3'(k2_xboole_0(A_43,B_44),B_45),A_43)
      | r1_xboole_0(k2_xboole_0(A_43,B_44),B_45) ) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_30,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_43,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    ! [C_26] :
      ( ~ r2_hidden(C_26,'#skF_8')
      | ~ r2_hidden(C_26,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_37,c_43])).

tff(c_72,plain,(
    ! [A_7] :
      ( ~ r2_hidden('#skF_3'(A_7,'#skF_7'),'#skF_8')
      | r1_xboole_0(A_7,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_470,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_3'(k2_xboole_0('#skF_8',B_55),'#skF_7'),B_55)
      | r1_xboole_0(k2_xboole_0('#skF_8',B_55),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_169,c_72])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_41,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_51,plain,(
    ! [C_25] :
      ( ~ r2_hidden(C_25,'#skF_9')
      | ~ r2_hidden(C_25,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_41,c_43])).

tff(c_61,plain,(
    ! [A_7] :
      ( ~ r2_hidden('#skF_3'(A_7,'#skF_7'),'#skF_9')
      | r1_xboole_0(A_7,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_509,plain,(
    r1_xboole_0(k2_xboole_0('#skF_8','#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_470,c_61])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_575,plain,(
    ! [C_58] :
      ( ~ r2_hidden(C_58,'#skF_7')
      | ~ r2_hidden(C_58,k2_xboole_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_509,c_20])).

tff(c_1900,plain,(
    ! [A_93] :
      ( ~ r2_hidden('#skF_3'(A_93,k2_xboole_0('#skF_8','#skF_9')),'#skF_7')
      | r1_xboole_0(A_93,k2_xboole_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_22,c_575])).

tff(c_1916,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_24,c_1900])).

tff(c_1923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_106,c_1916])).

tff(c_1925,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1954,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_36])).

tff(c_1955,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1954])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1924,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1932,plain,(
    ! [C_94] :
      ( ~ r2_hidden(C_94,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_94,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1924,c_20])).

tff(c_1967,plain,(
    ! [D_96] :
      ( ~ r2_hidden(D_96,'#skF_4')
      | ~ r2_hidden(D_96,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_1932])).

tff(c_1999,plain,(
    ! [A_98] :
      ( ~ r2_hidden('#skF_3'(A_98,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_98,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1967])).

tff(c_2003,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1999])).

tff(c_2007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1955,c_1955,c_2003])).

tff(c_2008,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1954])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2043,plain,(
    ! [D_103] :
      ( ~ r2_hidden(D_103,'#skF_4')
      | ~ r2_hidden(D_103,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_1932])).

tff(c_2120,plain,(
    ! [A_112] :
      ( ~ r2_hidden('#skF_3'(A_112,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_112,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_2043])).

tff(c_2124,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_2120])).

tff(c_2128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2008,c_2008,c_2124])).

tff(c_2130,plain,(
    ~ r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2133,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2130,c_28])).

tff(c_2134,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2133])).

tff(c_2129,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2135,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r1_xboole_0(A_115,B_116)
      | ~ r2_hidden(C_117,B_116)
      | ~ r2_hidden(C_117,A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2154,plain,(
    ! [C_119] :
      ( ~ r2_hidden(C_119,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_119,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2129,c_2135])).

tff(c_2186,plain,(
    ! [D_121] :
      ( ~ r2_hidden(D_121,'#skF_4')
      | ~ r2_hidden(D_121,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_2154])).

tff(c_2250,plain,(
    ! [A_129] :
      ( ~ r2_hidden('#skF_3'(A_129,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_129,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_2186])).

tff(c_2254,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_2250])).

tff(c_2258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2134,c_2134,c_2254])).

tff(c_2259,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2133])).

tff(c_2262,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r1_xboole_0(A_130,B_131)
      | ~ r2_hidden(C_132,B_131)
      | ~ r2_hidden(C_132,A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2296,plain,(
    ! [C_135] :
      ( ~ r2_hidden(C_135,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_135,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2129,c_2262])).

tff(c_2317,plain,(
    ! [D_136] :
      ( ~ r2_hidden(D_136,'#skF_4')
      | ~ r2_hidden(D_136,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_2296])).

tff(c_2360,plain,(
    ! [A_141] :
      ( ~ r2_hidden('#skF_3'(A_141,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_141,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_2317])).

tff(c_2364,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_2360])).

tff(c_2368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2259,c_2259,c_2364])).

tff(c_2370,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2376,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2370,c_32])).

tff(c_2377,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2376])).

tff(c_2369,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2378,plain,(
    ! [A_152,B_153,C_154] :
      ( ~ r1_xboole_0(A_152,B_153)
      | ~ r2_hidden(C_154,B_153)
      | ~ r2_hidden(C_154,A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2382,plain,(
    ! [C_155] :
      ( ~ r2_hidden(C_155,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_155,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2369,c_2378])).

tff(c_2414,plain,(
    ! [D_157] :
      ( ~ r2_hidden(D_157,'#skF_4')
      | ~ r2_hidden(D_157,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_2382])).

tff(c_2444,plain,(
    ! [A_160] :
      ( ~ r2_hidden('#skF_3'(A_160,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_160,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_2414])).

tff(c_2448,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_2444])).

tff(c_2452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2377,c_2377,c_2448])).

tff(c_2453,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2376])).

tff(c_2457,plain,(
    ! [A_161,B_162,C_163] :
      ( ~ r1_xboole_0(A_161,B_162)
      | ~ r2_hidden(C_163,B_162)
      | ~ r2_hidden(C_163,A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2476,plain,(
    ! [C_165] :
      ( ~ r2_hidden(C_165,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_165,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2369,c_2457])).

tff(c_2497,plain,(
    ! [D_166] :
      ( ~ r2_hidden(D_166,'#skF_4')
      | ~ r2_hidden(D_166,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_2476])).

tff(c_2554,plain,(
    ! [A_173] :
      ( ~ r2_hidden('#skF_3'(A_173,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_173,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_2497])).

tff(c_2558,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_2554])).

tff(c_2562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2453,c_2453,c_2558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:33:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.82  
% 4.35/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.82  %$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 4.35/1.82  
% 4.35/1.82  %Foreground sorts:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Background operators:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Foreground operators:
% 4.35/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.35/1.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.35/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.35/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.35/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.35/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.35/1.82  tff('#skF_9', type, '#skF_9': $i).
% 4.35/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.35/1.83  
% 4.35/1.84  tff(f_69, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.35/1.84  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.35/1.84  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.35/1.84  tff(c_34, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | ~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.84  tff(c_106, plain, (~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_34])).
% 4.35/1.84  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_107, plain, (![D_31, B_32, A_33]: (r2_hidden(D_31, B_32) | r2_hidden(D_31, A_33) | ~r2_hidden(D_31, k2_xboole_0(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.35/1.84  tff(c_169, plain, (![A_43, B_44, B_45]: (r2_hidden('#skF_3'(k2_xboole_0(A_43, B_44), B_45), B_44) | r2_hidden('#skF_3'(k2_xboole_0(A_43, B_44), B_45), A_43) | r1_xboole_0(k2_xboole_0(A_43, B_44), B_45))), inference(resolution, [status(thm)], [c_24, c_107])).
% 4.35/1.84  tff(c_30, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.84  tff(c_37, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_30])).
% 4.35/1.84  tff(c_43, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_62, plain, (![C_26]: (~r2_hidden(C_26, '#skF_8') | ~r2_hidden(C_26, '#skF_7'))), inference(resolution, [status(thm)], [c_37, c_43])).
% 4.35/1.84  tff(c_72, plain, (![A_7]: (~r2_hidden('#skF_3'(A_7, '#skF_7'), '#skF_8') | r1_xboole_0(A_7, '#skF_7'))), inference(resolution, [status(thm)], [c_22, c_62])).
% 4.35/1.84  tff(c_470, plain, (![B_55]: (r2_hidden('#skF_3'(k2_xboole_0('#skF_8', B_55), '#skF_7'), B_55) | r1_xboole_0(k2_xboole_0('#skF_8', B_55), '#skF_7'))), inference(resolution, [status(thm)], [c_169, c_72])).
% 4.35/1.84  tff(c_26, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | r1_xboole_0('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.84  tff(c_41, plain, (r1_xboole_0('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_26])).
% 4.35/1.84  tff(c_51, plain, (![C_25]: (~r2_hidden(C_25, '#skF_9') | ~r2_hidden(C_25, '#skF_7'))), inference(resolution, [status(thm)], [c_41, c_43])).
% 4.35/1.84  tff(c_61, plain, (![A_7]: (~r2_hidden('#skF_3'(A_7, '#skF_7'), '#skF_9') | r1_xboole_0(A_7, '#skF_7'))), inference(resolution, [status(thm)], [c_22, c_51])).
% 4.35/1.84  tff(c_509, plain, (r1_xboole_0(k2_xboole_0('#skF_8', '#skF_9'), '#skF_7')), inference(resolution, [status(thm)], [c_470, c_61])).
% 4.35/1.84  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_575, plain, (![C_58]: (~r2_hidden(C_58, '#skF_7') | ~r2_hidden(C_58, k2_xboole_0('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_509, c_20])).
% 4.35/1.84  tff(c_1900, plain, (![A_93]: (~r2_hidden('#skF_3'(A_93, k2_xboole_0('#skF_8', '#skF_9')), '#skF_7') | r1_xboole_0(A_93, k2_xboole_0('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_22, c_575])).
% 4.35/1.84  tff(c_1916, plain, (r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_24, c_1900])).
% 4.35/1.84  tff(c_1923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_106, c_1916])).
% 4.35/1.84  tff(c_1925, plain, (r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_34])).
% 4.35/1.84  tff(c_36, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.84  tff(c_1954, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1925, c_36])).
% 4.35/1.84  tff(c_1955, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1954])).
% 4.35/1.84  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.35/1.84  tff(c_1924, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_34])).
% 4.35/1.84  tff(c_1932, plain, (![C_94]: (~r2_hidden(C_94, k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_94, '#skF_4'))), inference(resolution, [status(thm)], [c_1924, c_20])).
% 4.35/1.84  tff(c_1967, plain, (![D_96]: (~r2_hidden(D_96, '#skF_4') | ~r2_hidden(D_96, '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_1932])).
% 4.35/1.84  tff(c_1999, plain, (![A_98]: (~r2_hidden('#skF_3'(A_98, '#skF_5'), '#skF_4') | r1_xboole_0(A_98, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_1967])).
% 4.35/1.84  tff(c_2003, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_1999])).
% 4.35/1.84  tff(c_2007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1955, c_1955, c_2003])).
% 4.35/1.84  tff(c_2008, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_1954])).
% 4.35/1.84  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.35/1.84  tff(c_2043, plain, (![D_103]: (~r2_hidden(D_103, '#skF_4') | ~r2_hidden(D_103, '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_1932])).
% 4.35/1.84  tff(c_2120, plain, (![A_112]: (~r2_hidden('#skF_3'(A_112, '#skF_6'), '#skF_4') | r1_xboole_0(A_112, '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_2043])).
% 4.35/1.84  tff(c_2124, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_2120])).
% 4.35/1.84  tff(c_2128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2008, c_2008, c_2124])).
% 4.35/1.84  tff(c_2130, plain, (~r1_xboole_0('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_26])).
% 4.35/1.84  tff(c_28, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.84  tff(c_2133, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2130, c_28])).
% 4.35/1.84  tff(c_2134, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2133])).
% 4.35/1.84  tff(c_2129, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_26])).
% 4.35/1.84  tff(c_2135, plain, (![A_115, B_116, C_117]: (~r1_xboole_0(A_115, B_116) | ~r2_hidden(C_117, B_116) | ~r2_hidden(C_117, A_115))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_2154, plain, (![C_119]: (~r2_hidden(C_119, k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_119, '#skF_4'))), inference(resolution, [status(thm)], [c_2129, c_2135])).
% 4.35/1.84  tff(c_2186, plain, (![D_121]: (~r2_hidden(D_121, '#skF_4') | ~r2_hidden(D_121, '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_2154])).
% 4.35/1.84  tff(c_2250, plain, (![A_129]: (~r2_hidden('#skF_3'(A_129, '#skF_5'), '#skF_4') | r1_xboole_0(A_129, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_2186])).
% 4.35/1.84  tff(c_2254, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_2250])).
% 4.35/1.84  tff(c_2258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2134, c_2134, c_2254])).
% 4.35/1.84  tff(c_2259, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_2133])).
% 4.35/1.84  tff(c_2262, plain, (![A_130, B_131, C_132]: (~r1_xboole_0(A_130, B_131) | ~r2_hidden(C_132, B_131) | ~r2_hidden(C_132, A_130))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_2296, plain, (![C_135]: (~r2_hidden(C_135, k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_135, '#skF_4'))), inference(resolution, [status(thm)], [c_2129, c_2262])).
% 4.35/1.84  tff(c_2317, plain, (![D_136]: (~r2_hidden(D_136, '#skF_4') | ~r2_hidden(D_136, '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_2296])).
% 4.35/1.84  tff(c_2360, plain, (![A_141]: (~r2_hidden('#skF_3'(A_141, '#skF_6'), '#skF_4') | r1_xboole_0(A_141, '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_2317])).
% 4.35/1.84  tff(c_2364, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_2360])).
% 4.35/1.84  tff(c_2368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2259, c_2259, c_2364])).
% 4.35/1.84  tff(c_2370, plain, (~r1_xboole_0('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_30])).
% 4.35/1.84  tff(c_32, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.84  tff(c_2376, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2370, c_32])).
% 4.35/1.84  tff(c_2377, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2376])).
% 4.35/1.84  tff(c_2369, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_30])).
% 4.35/1.84  tff(c_2378, plain, (![A_152, B_153, C_154]: (~r1_xboole_0(A_152, B_153) | ~r2_hidden(C_154, B_153) | ~r2_hidden(C_154, A_152))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_2382, plain, (![C_155]: (~r2_hidden(C_155, k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_155, '#skF_4'))), inference(resolution, [status(thm)], [c_2369, c_2378])).
% 4.35/1.84  tff(c_2414, plain, (![D_157]: (~r2_hidden(D_157, '#skF_4') | ~r2_hidden(D_157, '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_2382])).
% 4.35/1.84  tff(c_2444, plain, (![A_160]: (~r2_hidden('#skF_3'(A_160, '#skF_5'), '#skF_4') | r1_xboole_0(A_160, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_2414])).
% 4.35/1.84  tff(c_2448, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_2444])).
% 4.35/1.84  tff(c_2452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2377, c_2377, c_2448])).
% 4.35/1.84  tff(c_2453, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_2376])).
% 4.35/1.84  tff(c_2457, plain, (![A_161, B_162, C_163]: (~r1_xboole_0(A_161, B_162) | ~r2_hidden(C_163, B_162) | ~r2_hidden(C_163, A_161))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.84  tff(c_2476, plain, (![C_165]: (~r2_hidden(C_165, k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_165, '#skF_4'))), inference(resolution, [status(thm)], [c_2369, c_2457])).
% 4.35/1.84  tff(c_2497, plain, (![D_166]: (~r2_hidden(D_166, '#skF_4') | ~r2_hidden(D_166, '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_2476])).
% 4.35/1.84  tff(c_2554, plain, (![A_173]: (~r2_hidden('#skF_3'(A_173, '#skF_6'), '#skF_4') | r1_xboole_0(A_173, '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_2497])).
% 4.35/1.84  tff(c_2558, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_2554])).
% 4.35/1.84  tff(c_2562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2453, c_2453, c_2558])).
% 4.35/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.84  
% 4.35/1.84  Inference rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Ref     : 0
% 4.35/1.84  #Sup     : 479
% 4.35/1.84  #Fact    : 8
% 4.35/1.84  #Define  : 0
% 4.35/1.84  #Split   : 6
% 4.35/1.84  #Chain   : 0
% 4.35/1.84  #Close   : 0
% 4.35/1.84  
% 4.35/1.84  Ordering : KBO
% 4.35/1.84  
% 4.35/1.84  Simplification rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Subsume      : 79
% 4.35/1.84  #Demod        : 32
% 4.35/1.84  #Tautology    : 41
% 4.35/1.84  #SimpNegUnit  : 9
% 4.35/1.84  #BackRed      : 0
% 4.35/1.84  
% 4.35/1.84  #Partial instantiations: 0
% 4.35/1.84  #Strategies tried      : 1
% 4.35/1.84  
% 4.35/1.84  Timing (in seconds)
% 4.35/1.84  ----------------------
% 4.35/1.84  Preprocessing        : 0.29
% 4.35/1.84  Parsing              : 0.16
% 4.35/1.84  CNF conversion       : 0.02
% 4.35/1.84  Main loop            : 0.70
% 4.35/1.84  Inferencing          : 0.25
% 4.35/1.85  Reduction            : 0.17
% 4.35/1.85  Demodulation         : 0.11
% 4.35/1.85  BG Simplification    : 0.03
% 4.35/1.85  Subsumption          : 0.19
% 4.35/1.85  Abstraction          : 0.03
% 4.35/1.85  MUC search           : 0.00
% 4.35/1.85  Cooper               : 0.00
% 4.35/1.85  Total                : 1.03
% 4.35/1.85  Index Insertion      : 0.00
% 4.35/1.85  Index Deletion       : 0.00
% 4.35/1.85  Index Matching       : 0.00
% 4.35/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
