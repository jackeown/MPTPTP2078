%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:45 EST 2020

% Result     : Theorem 11.90s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 523 expanded)
%              Number of leaves         :   37 ( 188 expanded)
%              Depth                    :   14
%              Number of atoms          :  243 (1631 expanded)
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

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r2_hidden(k4_tarski(A,B),C)
          <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k1_wellord1(C,B)) )
       => k1_wellord1(k2_wellord1(C,k1_wellord1(C,B)),A) = k1_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k3_relat_1(k2_wellord1(B,A)),k3_relat_1(B))
        & r1_tarski(k3_relat_1(k2_wellord1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_80,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k2_wellord1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    v2_wellord1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_51] :
      ( v1_relat_2(A_51)
      | ~ v2_wellord1(A_51)
      | ~ v1_relat_1(A_51) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_134])).

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
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3301,plain,(
    ! [C_391,B_392,A_393] :
      ( r2_hidden(k4_tarski(C_391,B_392),A_393)
      | r2_hidden(k4_tarski(B_392,C_391),A_393)
      | C_391 = B_392
      | ~ r2_hidden(C_391,k3_relat_1(A_393))
      | ~ r2_hidden(B_392,k3_relat_1(A_393))
      | ~ v6_relat_2(A_393)
      | ~ v1_relat_1(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_88,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9')
    | r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_100,plain,(
    r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_82,plain,
    ( ~ r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8'))
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_127,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_82])).

tff(c_3320,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_7',k3_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ v6_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3301,c_127])).

tff(c_3354,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ v6_relat_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_76,c_3320])).

tff(c_3364,plain,(
    ~ v6_relat_2('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3354])).

tff(c_3370,plain,
    ( ~ v2_wellord1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_3364])).

tff(c_3377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3370])).

tff(c_3379,plain,(
    v6_relat_2('#skF_9') ),
    inference(splitRight,[status(thm)],[c_3354])).

tff(c_3343,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_7',k3_relat_1('#skF_9'))
    | ~ v6_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3301,c_127])).

tff(c_3362,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ v6_relat_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_3343])).

tff(c_3381,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_3362])).

tff(c_3382,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3381])).

tff(c_3386,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_127])).

tff(c_3397,plain,
    ( ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ v1_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_3386])).

tff(c_3404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_109,c_74,c_3397])).

tff(c_3406,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3381])).

tff(c_1742,plain,(
    ! [C_243,B_244,A_245] :
      ( r2_hidden(k4_tarski(C_243,B_244),A_245)
      | r2_hidden(k4_tarski(B_244,C_243),A_245)
      | C_243 = B_244
      | ~ r2_hidden(C_243,k3_relat_1(A_245))
      | ~ r2_hidden(B_244,k3_relat_1(A_245))
      | ~ v6_relat_2(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1758,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_7',k3_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_8',k3_relat_1('#skF_9'))
    | ~ v6_relat_2('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1742,c_127])).

tff(c_1788,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9')
    | '#skF_7' = '#skF_8'
    | ~ v6_relat_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_76,c_1758])).

tff(c_1797,plain,(
    ~ v6_relat_2('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1788])).

tff(c_1803,plain,
    ( ~ v2_wellord1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_1797])).

tff(c_1810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1803])).

tff(c_1811,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1788])).

tff(c_1813,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1811])).

tff(c_16,plain,(
    ! [D_22,A_11,B_18] :
      ( r2_hidden(D_22,k1_wellord1(A_11,B_18))
      | ~ r2_hidden(k4_tarski(D_22,B_18),A_11)
      | D_22 = B_18
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1816,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7'))
    | '#skF_7' = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1813,c_16])).

tff(c_1821,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7'))
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1816])).

tff(c_1823,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1821])).

tff(c_111,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,
    ( k1_wellord1('#skF_9','#skF_7') = k1_wellord1('#skF_9','#skF_8')
    | ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_100,c_111])).

tff(c_279,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_1851,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_279])).

tff(c_1861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1851])).

tff(c_1862,plain,(
    r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1821])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1898,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_8',B_250)
      | ~ r1_tarski(k1_wellord1('#skF_9','#skF_7'),B_250) ) ),
    inference(resolution,[status(thm)],[c_1862,c_2])).

tff(c_1922,plain,(
    r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_100,c_1898])).

tff(c_20,plain,(
    ! [D_22,A_11] :
      ( ~ r2_hidden(D_22,k1_wellord1(A_11,D_22))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1929,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1922,c_20])).

tff(c_1934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1929])).

tff(c_1935,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1811])).

tff(c_1963,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_279])).

tff(c_1973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1963])).

tff(c_1974,plain,(
    k1_wellord1('#skF_9','#skF_7') = k1_wellord1('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_3405,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_3381])).

tff(c_3409,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_7'))
    | '#skF_7' = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3405,c_16])).

tff(c_3414,plain,
    ( r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8'))
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1974,c_3409])).

tff(c_3415,plain,(
    r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_3406,c_3414])).

tff(c_2834,plain,(
    ! [C_362,B_363,A_364] :
      ( k1_wellord1(k2_wellord1(C_362,k1_wellord1(C_362,B_363)),A_364) = k1_wellord1(C_362,A_364)
      | ~ r2_hidden(A_364,k1_wellord1(C_362,B_363))
      | ~ v2_wellord1(C_362)
      | ~ v1_relat_1(C_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2908,plain,(
    ! [A_364] :
      ( k1_wellord1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')),A_364) = k1_wellord1('#skF_9',A_364)
      | ~ r2_hidden(A_364,k1_wellord1('#skF_9','#skF_7'))
      | ~ v2_wellord1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1974,c_2834])).

tff(c_2913,plain,(
    ! [A_365] :
      ( k1_wellord1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')),A_365) = k1_wellord1('#skF_9',A_365)
      | ~ r2_hidden(A_365,k1_wellord1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1974,c_2908])).

tff(c_2981,plain,(
    ! [A_365] :
      ( ~ r2_hidden(A_365,k1_wellord1('#skF_9',A_365))
      | ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')))
      | ~ r2_hidden(A_365,k1_wellord1('#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2913,c_20])).

tff(c_3062,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_2981])).

tff(c_3065,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_3062])).

tff(c_3069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3065])).

tff(c_3070,plain,(
    ! [A_365] :
      ( ~ r2_hidden(A_365,k1_wellord1('#skF_9',A_365))
      | ~ r2_hidden(A_365,k1_wellord1('#skF_9','#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_2981])).

tff(c_3434,plain,(
    ~ r2_hidden('#skF_8',k1_wellord1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3415,c_3070])).

tff(c_3443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_3434])).

tff(c_3444,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_3736,plain,(
    ! [D_476,A_477,B_478] :
      ( r2_hidden(D_476,k1_wellord1(A_477,B_478))
      | ~ r2_hidden(k4_tarski(D_476,B_478),A_477)
      | D_476 = B_478
      | ~ v1_relat_1(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3748,plain,
    ( r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8'))
    | '#skF_7' = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3444,c_3736])).

tff(c_3755,plain,
    ( r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8'))
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3748])).

tff(c_3756,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3755])).

tff(c_3448,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_7'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_82])).

tff(c_3762,plain,(
    ~ r1_tarski(k1_wellord1('#skF_9','#skF_8'),k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3756,c_3448])).

tff(c_3767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3762])).

tff(c_3768,plain,(
    r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3755])).

tff(c_4395,plain,(
    ! [C_568,B_569,A_570] :
      ( k1_wellord1(k2_wellord1(C_568,k1_wellord1(C_568,B_569)),A_570) = k1_wellord1(C_568,A_570)
      | ~ r2_hidden(A_570,k1_wellord1(C_568,B_569))
      | ~ v2_wellord1(C_568)
      | ~ v1_relat_1(C_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k1_wellord1(B_38,A_37),k3_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_11274,plain,(
    ! [C_970,A_971,B_972] :
      ( r1_tarski(k1_wellord1(C_970,A_971),k3_relat_1(k2_wellord1(C_970,k1_wellord1(C_970,B_972))))
      | ~ v1_relat_1(k2_wellord1(C_970,k1_wellord1(C_970,B_972)))
      | ~ r2_hidden(A_971,k1_wellord1(C_970,B_972))
      | ~ v2_wellord1(C_970)
      | ~ v1_relat_1(C_970) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4395,c_66])).

tff(c_68,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k3_relat_1(k2_wellord1(B_40,A_39)),A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3522,plain,(
    ! [A_420,C_421,B_422] :
      ( r1_tarski(A_420,C_421)
      | ~ r1_tarski(B_422,C_421)
      | ~ r1_tarski(A_420,B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3529,plain,(
    ! [A_420,A_39,B_40] :
      ( r1_tarski(A_420,A_39)
      | ~ r1_tarski(A_420,k3_relat_1(k2_wellord1(B_40,A_39)))
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_68,c_3522])).

tff(c_19039,plain,(
    ! [C_1313,A_1314,B_1315] :
      ( r1_tarski(k1_wellord1(C_1313,A_1314),k1_wellord1(C_1313,B_1315))
      | ~ v1_relat_1(k2_wellord1(C_1313,k1_wellord1(C_1313,B_1315)))
      | ~ r2_hidden(A_1314,k1_wellord1(C_1313,B_1315))
      | ~ v2_wellord1(C_1313)
      | ~ v1_relat_1(C_1313) ) ),
    inference(resolution,[status(thm)],[c_11274,c_3529])).

tff(c_19142,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8')))
    | ~ r2_hidden('#skF_7',k1_wellord1('#skF_9','#skF_8'))
    | ~ v2_wellord1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_19039,c_3448])).

tff(c_19196,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_9',k1_wellord1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3768,c_19142])).

tff(c_19199,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_19196])).

tff(c_19203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_19199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:39:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.90/5.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.90/5.43  
% 11.90/5.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.90/5.43  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_6
% 11.90/5.43  
% 11.90/5.43  %Foreground sorts:
% 11.90/5.43  
% 11.90/5.43  
% 11.90/5.43  %Background operators:
% 11.90/5.43  
% 11.90/5.43  
% 11.90/5.43  %Foreground operators:
% 11.90/5.43  tff('#skF_5', type, '#skF_5': $i > $i).
% 11.90/5.43  tff('#skF_4', type, '#skF_4': $i > $i).
% 11.90/5.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.90/5.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.90/5.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.90/5.43  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 11.90/5.43  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 11.90/5.43  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 11.90/5.43  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 11.90/5.43  tff('#skF_7', type, '#skF_7': $i).
% 11.90/5.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.90/5.43  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 11.90/5.43  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 11.90/5.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.90/5.43  tff('#skF_9', type, '#skF_9': $i).
% 11.90/5.43  tff('#skF_8', type, '#skF_8': $i).
% 11.90/5.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.90/5.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.90/5.43  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 11.90/5.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.90/5.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.90/5.43  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 11.90/5.43  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 11.90/5.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.90/5.43  tff('#skF_6', type, '#skF_6': $i > $i).
% 11.90/5.43  
% 12.04/5.45  tff(f_134, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 12.04/5.45  tff(f_75, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 12.04/5.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.04/5.45  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 12.04/5.45  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 12.04/5.45  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 12.04/5.45  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 12.04/5.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.04/5.45  tff(f_121, axiom, (![A, B, C]: (v1_relat_1(C) => ((v2_wellord1(C) & r2_hidden(A, k1_wellord1(C, B))) => (k1_wellord1(k2_wellord1(C, k1_wellord1(C, B)), A) = k1_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_wellord1)).
% 12.04/5.45  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_wellord1)).
% 12.04/5.45  tff(f_113, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k3_relat_1(k2_wellord1(B, A)), k3_relat_1(B)) & r1_tarski(k3_relat_1(k2_wellord1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_wellord1)).
% 12.04/5.45  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 12.04/5.45  tff(c_80, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.04/5.45  tff(c_46, plain, (![A_24, B_25]: (v1_relat_1(k2_wellord1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.04/5.45  tff(c_78, plain, (v2_wellord1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.04/5.45  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.04/5.45  tff(c_103, plain, (![A_51]: (v1_relat_2(A_51) | ~v2_wellord1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.04/5.45  tff(c_106, plain, (v1_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_78, c_103])).
% 12.04/5.45  tff(c_109, plain, (v1_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_106])).
% 12.04/5.45  tff(c_74, plain, (r2_hidden('#skF_8', k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.04/5.45  tff(c_48, plain, (![B_29, A_26]: (r2_hidden(k4_tarski(B_29, B_29), A_26) | ~r2_hidden(B_29, k3_relat_1(A_26)) | ~v1_relat_2(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.04/5.45  tff(c_38, plain, (![A_23]: (v6_relat_2(A_23) | ~v2_wellord1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.04/5.45  tff(c_76, plain, (r2_hidden('#skF_7', k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.04/5.45  tff(c_3301, plain, (![C_391, B_392, A_393]: (r2_hidden(k4_tarski(C_391, B_392), A_393) | r2_hidden(k4_tarski(B_392, C_391), A_393) | C_391=B_392 | ~r2_hidden(C_391, k3_relat_1(A_393)) | ~r2_hidden(B_392, k3_relat_1(A_393)) | ~v6_relat_2(A_393) | ~v1_relat_1(A_393))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.04/5.45  tff(c_88, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9') | r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.04/5.45  tff(c_100, plain, (r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_88])).
% 12.04/5.45  tff(c_82, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8')) | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.04/5.45  tff(c_127, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_82])).
% 12.04/5.45  tff(c_3320, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~r2_hidden('#skF_7', k3_relat_1('#skF_9')) | ~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~v6_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3301, c_127])).
% 12.04/5.45  tff(c_3354, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~v6_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_76, c_3320])).
% 12.04/5.45  tff(c_3364, plain, (~v6_relat_2('#skF_9')), inference(splitLeft, [status(thm)], [c_3354])).
% 12.04/5.45  tff(c_3370, plain, (~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_3364])).
% 12.04/5.45  tff(c_3377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3370])).
% 12.04/5.45  tff(c_3379, plain, (v6_relat_2('#skF_9')), inference(splitRight, [status(thm)], [c_3354])).
% 12.04/5.45  tff(c_3343, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~r2_hidden('#skF_7', k3_relat_1('#skF_9')) | ~v6_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3301, c_127])).
% 12.04/5.45  tff(c_3362, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~v6_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_3343])).
% 12.04/5.45  tff(c_3381, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_3362])).
% 12.04/5.45  tff(c_3382, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_3381])).
% 12.04/5.45  tff(c_3386, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_127])).
% 12.04/5.45  tff(c_3397, plain, (~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~v1_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_3386])).
% 12.04/5.45  tff(c_3404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_109, c_74, c_3397])).
% 12.04/5.45  tff(c_3406, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_3381])).
% 12.04/5.45  tff(c_1742, plain, (![C_243, B_244, A_245]: (r2_hidden(k4_tarski(C_243, B_244), A_245) | r2_hidden(k4_tarski(B_244, C_243), A_245) | C_243=B_244 | ~r2_hidden(C_243, k3_relat_1(A_245)) | ~r2_hidden(B_244, k3_relat_1(A_245)) | ~v6_relat_2(A_245) | ~v1_relat_1(A_245))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.04/5.45  tff(c_1758, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~r2_hidden('#skF_7', k3_relat_1('#skF_9')) | ~r2_hidden('#skF_8', k3_relat_1('#skF_9')) | ~v6_relat_2('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1742, c_127])).
% 12.04/5.45  tff(c_1788, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9') | '#skF_7'='#skF_8' | ~v6_relat_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_76, c_1758])).
% 12.04/5.45  tff(c_1797, plain, (~v6_relat_2('#skF_9')), inference(splitLeft, [status(thm)], [c_1788])).
% 12.04/5.45  tff(c_1803, plain, (~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_1797])).
% 12.04/5.45  tff(c_1810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1803])).
% 12.04/5.45  tff(c_1811, plain, ('#skF_7'='#skF_8' | r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_1788])).
% 12.04/5.45  tff(c_1813, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_1811])).
% 12.04/5.45  tff(c_16, plain, (![D_22, A_11, B_18]: (r2_hidden(D_22, k1_wellord1(A_11, B_18)) | ~r2_hidden(k4_tarski(D_22, B_18), A_11) | D_22=B_18 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.04/5.45  tff(c_1816, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7')) | '#skF_7'='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1813, c_16])).
% 12.04/5.45  tff(c_1821, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7')) | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1816])).
% 12.04/5.45  tff(c_1823, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_1821])).
% 12.04/5.45  tff(c_111, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.04/5.45  tff(c_116, plain, (k1_wellord1('#skF_9', '#skF_7')=k1_wellord1('#skF_9', '#skF_8') | ~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_100, c_111])).
% 12.04/5.45  tff(c_279, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_116])).
% 12.04/5.45  tff(c_1851, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_279])).
% 12.04/5.45  tff(c_1861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1851])).
% 12.04/5.45  tff(c_1862, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_1821])).
% 12.04/5.45  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.04/5.45  tff(c_1898, plain, (![B_250]: (r2_hidden('#skF_8', B_250) | ~r1_tarski(k1_wellord1('#skF_9', '#skF_7'), B_250))), inference(resolution, [status(thm)], [c_1862, c_2])).
% 12.04/5.45  tff(c_1922, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_100, c_1898])).
% 12.04/5.45  tff(c_20, plain, (![D_22, A_11]: (~r2_hidden(D_22, k1_wellord1(A_11, D_22)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.04/5.45  tff(c_1929, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1922, c_20])).
% 12.04/5.45  tff(c_1934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_1929])).
% 12.04/5.45  tff(c_1935, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_1811])).
% 12.04/5.45  tff(c_1963, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_279])).
% 12.04/5.45  tff(c_1973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1963])).
% 12.04/5.45  tff(c_1974, plain, (k1_wellord1('#skF_9', '#skF_7')=k1_wellord1('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_116])).
% 12.04/5.45  tff(c_3405, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_3381])).
% 12.04/5.45  tff(c_3409, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_7')) | '#skF_7'='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3405, c_16])).
% 12.04/5.45  tff(c_3414, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8')) | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1974, c_3409])).
% 12.04/5.45  tff(c_3415, plain, (r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_3406, c_3414])).
% 12.04/5.45  tff(c_2834, plain, (![C_362, B_363, A_364]: (k1_wellord1(k2_wellord1(C_362, k1_wellord1(C_362, B_363)), A_364)=k1_wellord1(C_362, A_364) | ~r2_hidden(A_364, k1_wellord1(C_362, B_363)) | ~v2_wellord1(C_362) | ~v1_relat_1(C_362))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.04/5.45  tff(c_2908, plain, (![A_364]: (k1_wellord1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')), A_364)=k1_wellord1('#skF_9', A_364) | ~r2_hidden(A_364, k1_wellord1('#skF_9', '#skF_7')) | ~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1974, c_2834])).
% 12.04/5.45  tff(c_2913, plain, (![A_365]: (k1_wellord1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')), A_365)=k1_wellord1('#skF_9', A_365) | ~r2_hidden(A_365, k1_wellord1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1974, c_2908])).
% 12.04/5.45  tff(c_2981, plain, (![A_365]: (~r2_hidden(A_365, k1_wellord1('#skF_9', A_365)) | ~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8'))) | ~r2_hidden(A_365, k1_wellord1('#skF_9', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2913, c_20])).
% 12.04/5.45  tff(c_3062, plain, (~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')))), inference(splitLeft, [status(thm)], [c_2981])).
% 12.04/5.45  tff(c_3065, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_3062])).
% 12.04/5.45  tff(c_3069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_3065])).
% 12.04/5.45  tff(c_3070, plain, (![A_365]: (~r2_hidden(A_365, k1_wellord1('#skF_9', A_365)) | ~r2_hidden(A_365, k1_wellord1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_2981])).
% 12.04/5.45  tff(c_3434, plain, (~r2_hidden('#skF_8', k1_wellord1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_3415, c_3070])).
% 12.04/5.45  tff(c_3443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3415, c_3434])).
% 12.04/5.45  tff(c_3444, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_88])).
% 12.04/5.45  tff(c_3736, plain, (![D_476, A_477, B_478]: (r2_hidden(D_476, k1_wellord1(A_477, B_478)) | ~r2_hidden(k4_tarski(D_476, B_478), A_477) | D_476=B_478 | ~v1_relat_1(A_477))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.04/5.45  tff(c_3748, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8')) | '#skF_7'='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3444, c_3736])).
% 12.04/5.45  tff(c_3755, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8')) | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3748])).
% 12.04/5.45  tff(c_3756, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_3755])).
% 12.04/5.45  tff(c_3448, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_7'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3444, c_82])).
% 12.04/5.45  tff(c_3762, plain, (~r1_tarski(k1_wellord1('#skF_9', '#skF_8'), k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3756, c_3448])).
% 12.04/5.45  tff(c_3767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3762])).
% 12.04/5.45  tff(c_3768, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_3755])).
% 12.04/5.45  tff(c_4395, plain, (![C_568, B_569, A_570]: (k1_wellord1(k2_wellord1(C_568, k1_wellord1(C_568, B_569)), A_570)=k1_wellord1(C_568, A_570) | ~r2_hidden(A_570, k1_wellord1(C_568, B_569)) | ~v2_wellord1(C_568) | ~v1_relat_1(C_568))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.04/5.45  tff(c_66, plain, (![B_38, A_37]: (r1_tarski(k1_wellord1(B_38, A_37), k3_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.04/5.45  tff(c_11274, plain, (![C_970, A_971, B_972]: (r1_tarski(k1_wellord1(C_970, A_971), k3_relat_1(k2_wellord1(C_970, k1_wellord1(C_970, B_972)))) | ~v1_relat_1(k2_wellord1(C_970, k1_wellord1(C_970, B_972))) | ~r2_hidden(A_971, k1_wellord1(C_970, B_972)) | ~v2_wellord1(C_970) | ~v1_relat_1(C_970))), inference(superposition, [status(thm), theory('equality')], [c_4395, c_66])).
% 12.04/5.45  tff(c_68, plain, (![B_40, A_39]: (r1_tarski(k3_relat_1(k2_wellord1(B_40, A_39)), A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.04/5.45  tff(c_3522, plain, (![A_420, C_421, B_422]: (r1_tarski(A_420, C_421) | ~r1_tarski(B_422, C_421) | ~r1_tarski(A_420, B_422))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.04/5.45  tff(c_3529, plain, (![A_420, A_39, B_40]: (r1_tarski(A_420, A_39) | ~r1_tarski(A_420, k3_relat_1(k2_wellord1(B_40, A_39))) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_68, c_3522])).
% 12.04/5.45  tff(c_19039, plain, (![C_1313, A_1314, B_1315]: (r1_tarski(k1_wellord1(C_1313, A_1314), k1_wellord1(C_1313, B_1315)) | ~v1_relat_1(k2_wellord1(C_1313, k1_wellord1(C_1313, B_1315))) | ~r2_hidden(A_1314, k1_wellord1(C_1313, B_1315)) | ~v2_wellord1(C_1313) | ~v1_relat_1(C_1313))), inference(resolution, [status(thm)], [c_11274, c_3529])).
% 12.04/5.45  tff(c_19142, plain, (~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8'))) | ~r2_hidden('#skF_7', k1_wellord1('#skF_9', '#skF_8')) | ~v2_wellord1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_19039, c_3448])).
% 12.04/5.45  tff(c_19196, plain, (~v1_relat_1(k2_wellord1('#skF_9', k1_wellord1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3768, c_19142])).
% 12.04/5.45  tff(c_19199, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_19196])).
% 12.04/5.45  tff(c_19203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_19199])).
% 12.04/5.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.04/5.45  
% 12.04/5.45  Inference rules
% 12.04/5.45  ----------------------
% 12.04/5.45  #Ref     : 0
% 12.04/5.45  #Sup     : 4560
% 12.04/5.45  #Fact    : 6
% 12.04/5.45  #Define  : 0
% 12.04/5.45  #Split   : 13
% 12.04/5.45  #Chain   : 0
% 12.04/5.45  #Close   : 0
% 12.04/5.45  
% 12.04/5.45  Ordering : KBO
% 12.04/5.45  
% 12.04/5.45  Simplification rules
% 12.04/5.45  ----------------------
% 12.04/5.45  #Subsume      : 283
% 12.04/5.45  #Demod        : 201
% 12.04/5.45  #Tautology    : 88
% 12.04/5.45  #SimpNegUnit  : 3
% 12.04/5.45  #BackRed      : 80
% 12.04/5.45  
% 12.04/5.45  #Partial instantiations: 0
% 12.04/5.45  #Strategies tried      : 1
% 12.04/5.45  
% 12.04/5.45  Timing (in seconds)
% 12.04/5.45  ----------------------
% 12.04/5.45  Preprocessing        : 0.35
% 12.04/5.45  Parsing              : 0.17
% 12.04/5.45  CNF conversion       : 0.03
% 12.04/5.45  Main loop            : 4.33
% 12.04/5.45  Inferencing          : 0.88
% 12.04/5.45  Reduction            : 0.77
% 12.04/5.45  Demodulation         : 0.51
% 12.04/5.45  BG Simplification    : 0.12
% 12.04/5.45  Subsumption          : 2.27
% 12.04/5.45  Abstraction          : 0.16
% 12.04/5.45  MUC search           : 0.00
% 12.04/5.45  Cooper               : 0.00
% 12.04/5.45  Total                : 4.72
% 12.04/5.45  Index Insertion      : 0.00
% 12.04/5.45  Index Deletion       : 0.00
% 12.04/5.45  Index Matching       : 0.00
% 12.04/5.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
