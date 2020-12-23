%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:45 EST 2020

% Result     : Theorem 12.86s
% Output     : CNFRefutation 13.09s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 529 expanded)
%              Number of leaves         :   37 ( 190 expanded)
%              Depth                    :   14
%              Number of atoms          :  254 (1648 expanded)
%              Number of equality atoms :   35 ( 153 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r2_hidden(k4_tarski(A,B),C)
          <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k1_wellord1(C,B)) )
       => k1_wellord1(k2_wellord1(C,k1_wellord1(C,B)),A) = k1_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_80,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k2_wellord1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    v2_wellord1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_52] :
      ( v1_relat_2(A_52)
      | ~ v2_wellord1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,
    ( v1_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_103])).

tff(c_109,plain,(
    v1_relat_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_106])).

tff(c_74,plain,(
    r2_hidden('#skF_8',k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_48,plain,(
    ! [B_29,A_26] :
      ( r2_hidden(k4_tarski(B_29,B_29),A_26)
      | ~ r2_hidden(B_29,k3_relat_1(A_26))
      | ~ v1_relat_2(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    ! [A_23] :
      ( v6_relat_2(A_23)
      | ~ v2_wellord1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    r2_hidden('#skF_7',k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2919,plain,(
    ! [C_377,B_378,A_379] :
      ( r2_hidden(k4_tarski(C_377,B_378),A_379)
      | r2_hidden(k4_tarski(B_378,C_377),A_379)
      | C_377 = B_378
      | ~ r2_hidden(C_377,k3_relat_1(A_379))
      | ~ r2_hidden(B_378,k3_relat_1(A_379))
      | ~ v6_relat_2(A_379)
      | ~ v1_relat_1(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_88,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9')
    | r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_100,plain,(
    r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_82,plain,
    ( ~ r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8'))
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_115,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_82])).

tff(c_2950,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_7',k3_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ v6_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2919,c_115])).

tff(c_2999,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ v6_relat_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_76,c_2950])).

tff(c_3012,plain,(
    ~ v6_relat_2('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2999])).

tff(c_3018,plain,
    ( ~ v2_wellord1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_3012])).

tff(c_3025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3018])).

tff(c_3027,plain,(
    v6_relat_2('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2999])).

tff(c_2985,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_7',k3_relat_1('#skF_9'))
    | ~ v6_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2919,c_115])).

tff(c_3010,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ v6_relat_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_2985])).

tff(c_3029,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_3010])).

tff(c_3030,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3029])).

tff(c_3034,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3030,c_115])).

tff(c_3045,plain,
    ( ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ v1_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_3034])).

tff(c_3052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_109,c_74,c_3045])).

tff(c_3054,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3029])).

tff(c_1341,plain,(
    ! [C_225,B_226,A_227] :
      ( r2_hidden(k4_tarski(C_225,B_226),A_227)
      | r2_hidden(k4_tarski(B_226,C_225),A_227)
      | C_225 = B_226
      | ~ r2_hidden(C_225,k3_relat_1(A_227))
      | ~ r2_hidden(B_226,k3_relat_1(A_227))
      | ~ v6_relat_2(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1369,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_7',k3_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ v6_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1341,c_115])).

tff(c_1414,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ v6_relat_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_76,c_1369])).

tff(c_1426,plain,(
    ~ v6_relat_2('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1414])).

tff(c_1432,plain,
    ( ~ v2_wellord1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_1426])).

tff(c_1439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1432])).

tff(c_1440,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1414])).

tff(c_1442,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1440])).

tff(c_16,plain,(
    ! [D_22,A_11,B_18] :
      ( r2_hidden(D_22,k1_wellord1(A_11,B_18))
      | ~ r2_hidden(k4_tarski(D_22,B_18),A_11)
      | D_22 = B_18
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1445,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7'))
    | '#skF_7' = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1442,c_16])).

tff(c_1450,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7'))
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1445])).

tff(c_1452,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1450])).

tff(c_116,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_124,plain,
    ( k1_wellord1('#skF_9','#skF_7') = k1_wellord1('#skF_9','#skF_8')
    | ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_100,c_116])).

tff(c_283,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_1472,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_283])).

tff(c_1482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1472])).

tff(c_1483,plain,(
    r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1450])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1514,plain,(
    ! [B_232] :
      ( r2_hidden('#skF_8',B_232)
      | ~ r1_tarski(k1_wellord1('#skF_9','#skF_7'),B_232) ) ),
    inference(resolution,[status(thm)],[c_1483,c_2])).

tff(c_1538,plain,(
    r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_100,c_1514])).

tff(c_20,plain,(
    ! [D_22,A_11] :
      ( ~ r2_hidden(D_22,k1_wellord1(A_11,D_22))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1545,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1538,c_20])).

tff(c_1550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1545])).

tff(c_1551,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1440])).

tff(c_1571,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_283])).

tff(c_1581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1571])).

tff(c_1582,plain,(
    k1_wellord1('#skF_9','#skF_7') = k1_wellord1('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_3053,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_3029])).

tff(c_3057,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7'))
    | '#skF_7' = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3053,c_16])).

tff(c_3062,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8'))
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1582,c_3057])).

tff(c_3063,plain,(
    r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_3054,c_3062])).

tff(c_2166,plain,(
    ! [C_323,B_324,A_325] :
      ( k1_wellord1(k2_wellord1(C_323,k1_wellord1(C_323,B_324)),A_325) = k1_wellord1(C_323,A_325)
      | ~ r2_hidden(A_325,k1_wellord1(C_323,B_324))
      | ~ v2_wellord1(C_323)
      | ~ v1_relat_1(C_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2231,plain,(
    ! [A_325] :
      ( k1_wellord1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')),A_325) = k1_wellord1('#skF_9',A_325)
      | ~ r2_hidden(A_325,k1_wellord1('#skF_9','#skF_7'))
      | ~ v2_wellord1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1582,c_2166])).

tff(c_2236,plain,(
    ! [A_326] :
      ( k1_wellord1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')),A_326) = k1_wellord1('#skF_9',A_326)
      | ~ r2_hidden(A_326,k1_wellord1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1582,c_2231])).

tff(c_2295,plain,(
    ! [A_326] :
      ( ~ r2_hidden(A_326,k1_wellord1('#skF_9',A_326))
      | ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')))
      | ~ r2_hidden(A_326,k1_wellord1('#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2236,c_20])).

tff(c_2338,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_2295])).

tff(c_2341,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_2338])).

tff(c_2345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2341])).

tff(c_2346,plain,(
    ! [A_326] :
      ( ~ r2_hidden(A_326,k1_wellord1('#skF_9',A_326))
      | ~ r2_hidden(A_326,k1_wellord1('#skF_9','#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_2295])).

tff(c_3066,plain,(
    ~ r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3063,c_2346])).

tff(c_3075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_3066])).

tff(c_3076,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_3395,plain,(
    ! [D_456,A_457,B_458] :
      ( r2_hidden(D_456,k1_wellord1(A_457,B_458))
      | ~ r2_hidden(k4_tarski(D_456,B_458),A_457)
      | D_456 = B_458
      | ~ v1_relat_1(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3407,plain,
    ( r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8'))
    | '#skF_7' = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3076,c_3395])).

tff(c_3414,plain,
    ( r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8'))
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3407])).

tff(c_3415,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3414])).

tff(c_3087,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_82])).

tff(c_3423,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_3087])).

tff(c_3428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3423])).

tff(c_3429,plain,(
    r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3414])).

tff(c_3787,plain,(
    ! [C_527,B_528,A_529] :
      ( k1_wellord1(k2_wellord1(C_527,k1_wellord1(C_527,B_528)),A_529) = k1_wellord1(C_527,A_529)
      | ~ r2_hidden(A_529,k1_wellord1(C_527,B_528))
      | ~ v2_wellord1(C_527)
      | ~ v1_relat_1(C_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k1_wellord1(B_38,A_37),k3_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_13356,plain,(
    ! [C_1061,A_1062,B_1063] :
      ( r1_tarski(k1_wellord1(C_1061,A_1062),k3_relat_1(k2_wellord1(C_1061,k1_wellord1(C_1061,B_1063))))
      | ~ v1_relat_1(k2_wellord1(C_1061,k1_wellord1(C_1061,B_1063)))
      | ~ r2_hidden(A_1062,k1_wellord1(C_1061,B_1063))
      | ~ v2_wellord1(C_1061)
      | ~ v1_relat_1(C_1061) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3787,c_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3176,plain,(
    ! [A_412,B_413,C_414] :
      ( r2_hidden(A_412,B_413)
      | ~ r2_hidden(A_412,k3_relat_1(k2_wellord1(C_414,B_413)))
      | ~ v1_relat_1(C_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3568,plain,(
    ! [C_495,B_496,B_497] :
      ( r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_495,B_496)),B_497),B_496)
      | ~ v1_relat_1(C_495)
      | r1_tarski(k3_relat_1(k2_wellord1(C_495,B_496)),B_497) ) ),
    inference(resolution,[status(thm)],[c_6,c_3176])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3587,plain,(
    ! [C_498,B_499] :
      ( ~ v1_relat_1(C_498)
      | r1_tarski(k3_relat_1(k2_wellord1(C_498,B_499)),B_499) ) ),
    inference(resolution,[status(thm)],[c_3568,c_4])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3619,plain,(
    ! [A_8,B_499,C_498] :
      ( r1_tarski(A_8,B_499)
      | ~ r1_tarski(A_8,k3_relat_1(k2_wellord1(C_498,B_499)))
      | ~ v1_relat_1(C_498) ) ),
    inference(resolution,[status(thm)],[c_3587,c_14])).

tff(c_20488,plain,(
    ! [C_1374,A_1375,B_1376] :
      ( r1_tarski(k1_wellord1(C_1374,A_1375),k1_wellord1(C_1374,B_1376))
      | ~ v1_relat_1(k2_wellord1(C_1374,k1_wellord1(C_1374,B_1376)))
      | ~ r2_hidden(A_1375,k1_wellord1(C_1374,B_1376))
      | ~ v2_wellord1(C_1374)
      | ~ v1_relat_1(C_1374) ) ),
    inference(resolution,[status(thm)],[c_13356,c_3619])).

tff(c_20602,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')))
    | ~ r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8'))
    | ~ v2_wellord1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_20488,c_3087])).

tff(c_20657,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3429,c_20602])).

tff(c_20660,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_20657])).

tff(c_20664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.86/6.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.98/6.29  
% 12.98/6.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.98/6.30  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_6
% 12.98/6.30  
% 12.98/6.30  %Foreground sorts:
% 12.98/6.30  
% 12.98/6.30  
% 12.98/6.30  %Background operators:
% 12.98/6.30  
% 12.98/6.30  
% 12.98/6.30  %Foreground operators:
% 12.98/6.30  tff('#skF_5', type, '#skF_5': $i > $i).
% 12.98/6.30  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.98/6.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.98/6.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.98/6.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.98/6.30  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 12.98/6.30  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 12.98/6.30  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 12.98/6.30  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 12.98/6.30  tff('#skF_7', type, '#skF_7': $i).
% 12.98/6.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.98/6.30  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 12.98/6.30  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 12.98/6.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.98/6.30  tff('#skF_9', type, '#skF_9': $i).
% 12.98/6.30  tff('#skF_8', type, '#skF_8': $i).
% 12.98/6.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.98/6.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.98/6.30  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 12.98/6.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.98/6.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.98/6.30  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 12.98/6.30  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 12.98/6.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.98/6.30  tff('#skF_6', type, '#skF_6': $i > $i).
% 12.98/6.30  
% 13.09/6.31  tff(f_136, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 13.09/6.31  tff(f_75, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 13.09/6.31  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.09/6.31  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 13.09/6.31  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 13.09/6.31  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 13.09/6.31  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 13.09/6.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.09/6.31  tff(f_123, axiom, (![A, B, C]: (v1_relat_1(C) => ((v2_wellord1(C) & r2_hidden(A, k1_wellord1(C, B))) => (k1_wellord1(k2_wellord1(C, k1_wellord1(C, B)), A) = k1_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_wellord1)).
% 13.09/6.31  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_wellord1)).
% 13.09/6.31  tff(f_115, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_wellord1)).
% 13.09/6.31  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.09/6.31  tff(c_80, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.09/6.31  tff(c_46, plain, (![A_24, B_25]: (v1_relat_1(k2_wellord1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.09/6.31  tff(c_78, plain, (v2_wellord1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.09/6.31  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.09/6.31  tff(c_103, plain, (![A_52]: (v1_relat_2(A_52) | ~v2_wellord1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.09/6.31  tff(c_106, plain, (v1_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_78, c_103])).
% 13.09/6.31  tff(c_109, plain, (v1_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_106])).
% 13.09/6.31  tff(c_74, plain, (r2_hidden('#skF_8', k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.09/6.31  tff(c_48, plain, (![B_29, A_26]: (r2_hidden(k4_tarski(B_29, B_29), A_26) | ~r2_hidden(B_29, k3_relat_1(A_26)) | ~v1_relat_2(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.09/6.31  tff(c_38, plain, (![A_23]: (v6_relat_2(A_23) | ~v2_wellord1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.09/6.31  tff(c_76, plain, (r2_hidden('#skF_7', k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.09/6.31  tff(c_2919, plain, (![C_377, B_378, A_379]: (r2_hidden(k4_tarski(C_377, B_378), A_379) | r2_hidden(k4_tarski(B_378, C_377), A_379) | C_377=B_378 | ~r2_hidden(C_377, k3_relat_1(A_379)) | ~r2_hidden(B_378, k3_relat_1(A_379)) | ~v6_relat_2(A_379) | ~v1_relat_1(A_379))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.09/6.31  tff(c_88, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9') | r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.09/6.31  tff(c_100, plain, (r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_88])).
% 13.09/6.31  tff(c_82, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8')) | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.09/6.31  tff(c_115, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_82])).
% 13.09/6.31  tff(c_2950, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~r2_hidden('#skF_7', k3_relat_1('#skF_9')) | ~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~v6_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2919, c_115])).
% 13.09/6.31  tff(c_2999, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~v6_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_76, c_2950])).
% 13.09/6.31  tff(c_3012, plain, (~v6_relat_2('#skF_9')), inference(splitLeft, [status(thm)], [c_2999])).
% 13.09/6.31  tff(c_3018, plain, (~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_3012])).
% 13.09/6.31  tff(c_3025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3018])).
% 13.09/6.31  tff(c_3027, plain, (v6_relat_2('#skF_9')), inference(splitRight, [status(thm)], [c_2999])).
% 13.09/6.31  tff(c_2985, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~r2_hidden('#skF_7', k3_relat_1('#skF_9')) | ~v6_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2919, c_115])).
% 13.09/6.31  tff(c_3010, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~v6_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_2985])).
% 13.09/6.31  tff(c_3029, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3027, c_3010])).
% 13.09/6.31  tff(c_3030, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_3029])).
% 13.09/6.31  tff(c_3034, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3030, c_115])).
% 13.09/6.31  tff(c_3045, plain, (~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~v1_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_3034])).
% 13.09/6.31  tff(c_3052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_109, c_74, c_3045])).
% 13.09/6.31  tff(c_3054, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_3029])).
% 13.09/6.31  tff(c_1341, plain, (![C_225, B_226, A_227]: (r2_hidden(k4_tarski(C_225, B_226), A_227) | r2_hidden(k4_tarski(B_226, C_225), A_227) | C_225=B_226 | ~r2_hidden(C_225, k3_relat_1(A_227)) | ~r2_hidden(B_226, k3_relat_1(A_227)) | ~v6_relat_2(A_227) | ~v1_relat_1(A_227))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.09/6.31  tff(c_1369, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~r2_hidden('#skF_7', k3_relat_1('#skF_9')) | ~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~v6_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1341, c_115])).
% 13.09/6.31  tff(c_1414, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~v6_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_76, c_1369])).
% 13.09/6.31  tff(c_1426, plain, (~v6_relat_2('#skF_9')), inference(splitLeft, [status(thm)], [c_1414])).
% 13.09/6.31  tff(c_1432, plain, (~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_1426])).
% 13.09/6.31  tff(c_1439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1432])).
% 13.09/6.31  tff(c_1440, plain, ('#skF_7'='#skF_8' | r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_1414])).
% 13.09/6.31  tff(c_1442, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_1440])).
% 13.09/6.31  tff(c_16, plain, (![D_22, A_11, B_18]: (r2_hidden(D_22, k1_wellord1(A_11, B_18)) | ~r2_hidden(k4_tarski(D_22, B_18), A_11) | D_22=B_18 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.09/6.31  tff(c_1445, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7')) | '#skF_7'='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1442, c_16])).
% 13.09/6.31  tff(c_1450, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7')) | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1445])).
% 13.09/6.31  tff(c_1452, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_1450])).
% 13.09/6.31  tff(c_116, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.09/6.31  tff(c_124, plain, (k1_wellord1('#skF_9', '#skF_7')=k1_wellord1('#skF_9', '#skF_8') | ~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_100, c_116])).
% 13.09/6.31  tff(c_283, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_124])).
% 13.09/6.31  tff(c_1472, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_283])).
% 13.09/6.31  tff(c_1482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1472])).
% 13.09/6.31  tff(c_1483, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_1450])).
% 13.09/6.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.09/6.31  tff(c_1514, plain, (![B_232]: (r2_hidden('#skF_8', B_232) | ~r1_tarski(k1_wellord1('#skF_9', '#skF_7'), B_232))), inference(resolution, [status(thm)], [c_1483, c_2])).
% 13.09/6.31  tff(c_1538, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_100, c_1514])).
% 13.09/6.31  tff(c_20, plain, (![D_22, A_11]: (~r2_hidden(D_22, k1_wellord1(A_11, D_22)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.09/6.31  tff(c_1545, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1538, c_20])).
% 13.09/6.31  tff(c_1550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_1545])).
% 13.09/6.31  tff(c_1551, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_1440])).
% 13.09/6.31  tff(c_1571, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_283])).
% 13.09/6.31  tff(c_1581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1571])).
% 13.09/6.31  tff(c_1582, plain, (k1_wellord1('#skF_9', '#skF_7')=k1_wellord1('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_124])).
% 13.09/6.31  tff(c_3053, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_3029])).
% 13.09/6.31  tff(c_3057, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7')) | '#skF_7'='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3053, c_16])).
% 13.09/6.31  tff(c_3062, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8')) | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1582, c_3057])).
% 13.09/6.31  tff(c_3063, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_3054, c_3062])).
% 13.09/6.31  tff(c_2166, plain, (![C_323, B_324, A_325]: (k1_wellord1(k2_wellord1(C_323, k1_wellord1(C_323, B_324)), A_325)=k1_wellord1(C_323, A_325) | ~r2_hidden(A_325, k1_wellord1(C_323, B_324)) | ~v2_wellord1(C_323) | ~v1_relat_1(C_323))), inference(cnfTransformation, [status(thm)], [f_123])).
% 13.09/6.31  tff(c_2231, plain, (![A_325]: (k1_wellord1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')), A_325)=k1_wellord1('#skF_9', A_325) | ~r2_hidden(A_325, k1_wellord1('#skF_9', '#skF_7')) | ~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1582, c_2166])).
% 13.09/6.31  tff(c_2236, plain, (![A_326]: (k1_wellord1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')), A_326)=k1_wellord1('#skF_9', A_326) | ~r2_hidden(A_326, k1_wellord1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1582, c_2231])).
% 13.09/6.31  tff(c_2295, plain, (![A_326]: (~r2_hidden(A_326, k1_wellord1('#skF_9', A_326)) | ~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8'))) | ~r2_hidden(A_326, k1_wellord1('#skF_9', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2236, c_20])).
% 13.09/6.31  tff(c_2338, plain, (~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')))), inference(splitLeft, [status(thm)], [c_2295])).
% 13.09/6.31  tff(c_2341, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_2338])).
% 13.09/6.31  tff(c_2345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2341])).
% 13.09/6.31  tff(c_2346, plain, (![A_326]: (~r2_hidden(A_326, k1_wellord1('#skF_9', A_326)) | ~r2_hidden(A_326, k1_wellord1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_2295])).
% 13.09/6.31  tff(c_3066, plain, (~r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_3063, c_2346])).
% 13.09/6.31  tff(c_3075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3063, c_3066])).
% 13.09/6.31  tff(c_3076, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_88])).
% 13.09/6.31  tff(c_3395, plain, (![D_456, A_457, B_458]: (r2_hidden(D_456, k1_wellord1(A_457, B_458)) | ~r2_hidden(k4_tarski(D_456, B_458), A_457) | D_456=B_458 | ~v1_relat_1(A_457))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.09/6.31  tff(c_3407, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8')) | '#skF_7'='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3076, c_3395])).
% 13.09/6.31  tff(c_3414, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8')) | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3407])).
% 13.09/6.31  tff(c_3415, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_3414])).
% 13.09/6.31  tff(c_3087, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3076, c_82])).
% 13.09/6.31  tff(c_3423, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_3087])).
% 13.09/6.31  tff(c_3428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3423])).
% 13.09/6.31  tff(c_3429, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_3414])).
% 13.09/6.31  tff(c_3787, plain, (![C_527, B_528, A_529]: (k1_wellord1(k2_wellord1(C_527, k1_wellord1(C_527, B_528)), A_529)=k1_wellord1(C_527, A_529) | ~r2_hidden(A_529, k1_wellord1(C_527, B_528)) | ~v2_wellord1(C_527) | ~v1_relat_1(C_527))), inference(cnfTransformation, [status(thm)], [f_123])).
% 13.09/6.31  tff(c_66, plain, (![B_38, A_37]: (r1_tarski(k1_wellord1(B_38, A_37), k3_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.09/6.31  tff(c_13356, plain, (![C_1061, A_1062, B_1063]: (r1_tarski(k1_wellord1(C_1061, A_1062), k3_relat_1(k2_wellord1(C_1061, k1_wellord1(C_1061, B_1063)))) | ~v1_relat_1(k2_wellord1(C_1061, k1_wellord1(C_1061, B_1063))) | ~r2_hidden(A_1062, k1_wellord1(C_1061, B_1063)) | ~v2_wellord1(C_1061) | ~v1_relat_1(C_1061))), inference(superposition, [status(thm), theory('equality')], [c_3787, c_66])).
% 13.09/6.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.09/6.31  tff(c_3176, plain, (![A_412, B_413, C_414]: (r2_hidden(A_412, B_413) | ~r2_hidden(A_412, k3_relat_1(k2_wellord1(C_414, B_413))) | ~v1_relat_1(C_414))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.09/6.31  tff(c_3568, plain, (![C_495, B_496, B_497]: (r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_495, B_496)), B_497), B_496) | ~v1_relat_1(C_495) | r1_tarski(k3_relat_1(k2_wellord1(C_495, B_496)), B_497))), inference(resolution, [status(thm)], [c_6, c_3176])).
% 13.09/6.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.09/6.31  tff(c_3587, plain, (![C_498, B_499]: (~v1_relat_1(C_498) | r1_tarski(k3_relat_1(k2_wellord1(C_498, B_499)), B_499))), inference(resolution, [status(thm)], [c_3568, c_4])).
% 13.09/6.31  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.09/6.31  tff(c_3619, plain, (![A_8, B_499, C_498]: (r1_tarski(A_8, B_499) | ~r1_tarski(A_8, k3_relat_1(k2_wellord1(C_498, B_499))) | ~v1_relat_1(C_498))), inference(resolution, [status(thm)], [c_3587, c_14])).
% 13.09/6.31  tff(c_20488, plain, (![C_1374, A_1375, B_1376]: (r1_tarski(k1_wellord1(C_1374, A_1375), k1_wellord1(C_1374, B_1376)) | ~v1_relat_1(k2_wellord1(C_1374, k1_wellord1(C_1374, B_1376))) | ~r2_hidden(A_1375, k1_wellord1(C_1374, B_1376)) | ~v2_wellord1(C_1374) | ~v1_relat_1(C_1374))), inference(resolution, [status(thm)], [c_13356, c_3619])).
% 13.09/6.31  tff(c_20602, plain, (~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8'))) | ~r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8')) | ~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_20488, c_3087])).
% 13.09/6.31  tff(c_20657, plain, (~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3429, c_20602])).
% 13.09/6.31  tff(c_20660, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_20657])).
% 13.09/6.31  tff(c_20664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_20660])).
% 13.09/6.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.09/6.31  
% 13.09/6.31  Inference rules
% 13.09/6.31  ----------------------
% 13.09/6.31  #Ref     : 0
% 13.09/6.31  #Sup     : 4860
% 13.09/6.31  #Fact    : 6
% 13.09/6.31  #Define  : 0
% 13.09/6.31  #Split   : 13
% 13.09/6.31  #Chain   : 0
% 13.09/6.31  #Close   : 0
% 13.09/6.31  
% 13.09/6.31  Ordering : KBO
% 13.09/6.32  
% 13.09/6.32  Simplification rules
% 13.09/6.32  ----------------------
% 13.09/6.32  #Subsume      : 311
% 13.09/6.32  #Demod        : 212
% 13.09/6.32  #Tautology    : 95
% 13.09/6.32  #SimpNegUnit  : 3
% 13.09/6.32  #BackRed      : 68
% 13.09/6.32  
% 13.09/6.32  #Partial instantiations: 0
% 13.09/6.32  #Strategies tried      : 1
% 13.09/6.32  
% 13.09/6.32  Timing (in seconds)
% 13.09/6.32  ----------------------
% 13.09/6.32  Preprocessing        : 0.37
% 13.09/6.32  Parsing              : 0.19
% 13.09/6.32  CNF conversion       : 0.03
% 13.09/6.32  Main loop            : 5.12
% 13.09/6.32  Inferencing          : 0.96
% 13.09/6.32  Reduction            : 0.81
% 13.09/6.32  Demodulation         : 0.53
% 13.09/6.32  BG Simplification    : 0.14
% 13.09/6.32  Subsumption          : 2.85
% 13.09/6.32  Abstraction          : 0.21
% 13.09/6.32  MUC search           : 0.00
% 13.09/6.32  Cooper               : 0.00
% 13.09/6.32  Total                : 5.53
% 13.09/6.32  Index Insertion      : 0.00
% 13.09/6.32  Index Deletion       : 0.00
% 13.09/6.32  Index Matching       : 0.00
% 13.09/6.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
