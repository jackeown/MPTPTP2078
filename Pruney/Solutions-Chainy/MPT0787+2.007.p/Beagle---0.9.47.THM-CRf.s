%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:46 EST 2020

% Result     : Theorem 15.98s
% Output     : CNFRefutation 15.98s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 299 expanded)
%              Number of leaves         :   39 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :  218 ( 907 expanded)
%              Number of equality atoms :   19 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_9 > #skF_7 > #skF_5 > #skF_11 > #skF_4 > #skF_15 > #skF_8 > #skF_12 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r2_hidden(k4_tarski(A,B),C)
          <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_106,axiom,(
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

tff(f_53,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> ! [B,C,D] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,D),A) )
           => r2_hidden(k4_tarski(B,D),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ( v2_wellord1(B)
          & r1_tarski(A,k3_relat_1(B)) )
       => ( ~ ( A != k3_relat_1(B)
              & ! [C] :
                  ~ ( r2_hidden(C,k3_relat_1(B))
                    & A = k1_wellord1(B,C) ) )
        <=> ! [C] :
              ( r2_hidden(C,A)
             => ! [D] :
                  ( r2_hidden(k4_tarski(D,C),B)
                 => r2_hidden(D,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

tff(c_90,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_88,plain,(
    v2_wellord1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_106,plain,(
    ! [A_59] :
      ( v1_relat_2(A_59)
      | ~ v2_wellord1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,
    ( v1_relat_2('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_88,c_106])).

tff(c_112,plain,(
    v1_relat_2('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_109])).

tff(c_86,plain,(
    r2_hidden('#skF_13',k3_relat_1('#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    ! [B_25,A_22] :
      ( r2_hidden(k4_tarski(B_25,B_25),A_22)
      | ~ r2_hidden(B_25,k3_relat_1(A_22))
      | ~ v1_relat_2(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_98,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_14'),'#skF_15')
    | r1_tarski(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_114,plain,(
    r1_tarski(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_34,plain,(
    ! [A_21] :
      ( v6_relat_2(A_21)
      | ~ v2_wellord1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,(
    r2_hidden('#skF_14',k3_relat_1('#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1412,plain,(
    ! [C_267,B_268,A_269] :
      ( r2_hidden(k4_tarski(C_267,B_268),A_269)
      | r2_hidden(k4_tarski(B_268,C_267),A_269)
      | C_267 = B_268
      | ~ r2_hidden(C_267,k3_relat_1(A_269))
      | ~ r2_hidden(B_268,k3_relat_1(A_269))
      | ~ v6_relat_2(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [D_20,A_9,B_16] :
      ( r2_hidden(D_20,k1_wellord1(A_9,B_16))
      | ~ r2_hidden(k4_tarski(D_20,B_16),A_9)
      | D_20 = B_16
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14638,plain,(
    ! [C_941,A_942,B_943] :
      ( r2_hidden(C_941,k1_wellord1(A_942,B_943))
      | r2_hidden(k4_tarski(B_943,C_941),A_942)
      | C_941 = B_943
      | ~ r2_hidden(C_941,k3_relat_1(A_942))
      | ~ r2_hidden(B_943,k3_relat_1(A_942))
      | ~ v6_relat_2(A_942)
      | ~ v1_relat_1(A_942) ) ),
    inference(resolution,[status(thm)],[c_1412,c_12])).

tff(c_92,plain,
    ( ~ r1_tarski(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14'))
    | ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),'#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_129,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_92])).

tff(c_14703,plain,
    ( r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13'))
    | '#skF_14' = '#skF_13'
    | ~ r2_hidden('#skF_14',k3_relat_1('#skF_15'))
    | ~ r2_hidden('#skF_13',k3_relat_1('#skF_15'))
    | ~ v6_relat_2('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_14638,c_129])).

tff(c_14730,plain,
    ( r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13'))
    | '#skF_14' = '#skF_13'
    | ~ v6_relat_2('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_14703])).

tff(c_14732,plain,(
    ~ v6_relat_2('#skF_15') ),
    inference(splitLeft,[status(thm)],[c_14730])).

tff(c_14738,plain,
    ( ~ v2_wellord1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_34,c_14732])).

tff(c_14745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_14738])).

tff(c_14746,plain,
    ( '#skF_14' = '#skF_13'
    | r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13')) ),
    inference(splitRight,[status(thm)],[c_14730])).

tff(c_14748,plain,(
    r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_14746])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14770,plain,(
    ! [B_944] :
      ( r2_hidden('#skF_14',B_944)
      | ~ r1_tarski(k1_wellord1('#skF_15','#skF_13'),B_944) ) ),
    inference(resolution,[status(thm)],[c_14748,c_2])).

tff(c_14840,plain,(
    r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_14')) ),
    inference(resolution,[status(thm)],[c_114,c_14770])).

tff(c_16,plain,(
    ! [D_20,A_9] :
      ( ~ r2_hidden(D_20,k1_wellord1(A_9,D_20))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14852,plain,(
    ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_14840,c_16])).

tff(c_14868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_14852])).

tff(c_14869,plain,(
    '#skF_14' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_14746])).

tff(c_14940,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_13'),'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14869,c_129])).

tff(c_14961,plain,
    ( ~ r2_hidden('#skF_13',k3_relat_1('#skF_15'))
    | ~ v1_relat_2('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_42,c_14940])).

tff(c_14973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_112,c_86,c_14961])).

tff(c_14974,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_14'),'#skF_15') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_14977,plain,(
    ~ r1_tarski(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14974,c_92])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [D_20,B_16,A_9] :
      ( r2_hidden(k4_tarski(D_20,B_16),A_9)
      | ~ r2_hidden(D_20,k1_wellord1(A_9,B_16))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_21] :
      ( v8_relat_2(A_21)
      | ~ v2_wellord1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_15799,plain,(
    ! [B_1089,D_1090,A_1091,C_1092] :
      ( r2_hidden(k4_tarski(B_1089,D_1090),A_1091)
      | ~ r2_hidden(k4_tarski(C_1092,D_1090),A_1091)
      | ~ r2_hidden(k4_tarski(B_1089,C_1092),A_1091)
      | ~ v8_relat_2(A_1091)
      | ~ v1_relat_1(A_1091) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_15824,plain,(
    ! [B_1089] :
      ( r2_hidden(k4_tarski(B_1089,'#skF_14'),'#skF_15')
      | ~ r2_hidden(k4_tarski(B_1089,'#skF_13'),'#skF_15')
      | ~ v8_relat_2('#skF_15')
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_14974,c_15799])).

tff(c_15837,plain,(
    ! [B_1089] :
      ( r2_hidden(k4_tarski(B_1089,'#skF_14'),'#skF_15')
      | ~ r2_hidden(k4_tarski(B_1089,'#skF_13'),'#skF_15')
      | ~ v8_relat_2('#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15824])).

tff(c_15838,plain,(
    ~ v8_relat_2('#skF_15') ),
    inference(splitLeft,[status(thm)],[c_15837])).

tff(c_15841,plain,
    ( ~ v2_wellord1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_38,c_15838])).

tff(c_15845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_15841])).

tff(c_15887,plain,(
    ! [B_1095] :
      ( r2_hidden(k4_tarski(B_1095,'#skF_14'),'#skF_15')
      | ~ r2_hidden(k4_tarski(B_1095,'#skF_13'),'#skF_15') ) ),
    inference(splitRight,[status(thm)],[c_15837])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r2_hidden(A_6,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15898,plain,(
    ! [B_1095] :
      ( r2_hidden(B_1095,k3_relat_1('#skF_15'))
      | ~ v1_relat_1('#skF_15')
      | ~ r2_hidden(k4_tarski(B_1095,'#skF_13'),'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_15887,c_10])).

tff(c_15914,plain,(
    ! [B_1096] :
      ( r2_hidden(B_1096,k3_relat_1('#skF_15'))
      | ~ r2_hidden(k4_tarski(B_1096,'#skF_13'),'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15898])).

tff(c_15922,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,k3_relat_1('#skF_15'))
      | ~ r2_hidden(D_20,k1_wellord1('#skF_15','#skF_13'))
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_14,c_15914])).

tff(c_15929,plain,(
    ! [D_1097] :
      ( r2_hidden(D_1097,k3_relat_1('#skF_15'))
      | ~ r2_hidden(D_1097,k1_wellord1('#skF_15','#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15922])).

tff(c_16204,plain,(
    ! [B_1108] :
      ( r2_hidden('#skF_1'(k1_wellord1('#skF_15','#skF_13'),B_1108),k3_relat_1('#skF_15'))
      | r1_tarski(k1_wellord1('#skF_15','#skF_13'),B_1108) ) ),
    inference(resolution,[status(thm)],[c_6,c_15929])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16212,plain,(
    r1_tarski(k1_wellord1('#skF_15','#skF_13'),k3_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_16204,c_4])).

tff(c_18742,plain,(
    ! [C_1296,B_1297,D_1298,C_1299] :
      ( ~ r2_hidden(C_1296,k3_relat_1(B_1297))
      | r2_hidden(D_1298,k1_wellord1(B_1297,C_1296))
      | ~ r2_hidden(k4_tarski(D_1298,C_1299),B_1297)
      | ~ r2_hidden(C_1299,k1_wellord1(B_1297,C_1296))
      | ~ r1_tarski(k1_wellord1(B_1297,C_1296),k3_relat_1(B_1297))
      | ~ v2_wellord1(B_1297)
      | ~ v1_relat_1(B_1297) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_18795,plain,(
    ! [C_1296] :
      ( ~ r2_hidden(C_1296,k3_relat_1('#skF_15'))
      | r2_hidden('#skF_13',k1_wellord1('#skF_15',C_1296))
      | ~ r2_hidden('#skF_14',k1_wellord1('#skF_15',C_1296))
      | ~ r1_tarski(k1_wellord1('#skF_15',C_1296),k3_relat_1('#skF_15'))
      | ~ v2_wellord1('#skF_15')
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_14974,c_18742])).

tff(c_18878,plain,(
    ! [C_1304] :
      ( ~ r2_hidden(C_1304,k3_relat_1('#skF_15'))
      | r2_hidden('#skF_13',k1_wellord1('#skF_15',C_1304))
      | ~ r2_hidden('#skF_14',k1_wellord1('#skF_15',C_1304))
      | ~ r1_tarski(k1_wellord1('#skF_15',C_1304),k3_relat_1('#skF_15')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_18795])).

tff(c_18895,plain,
    ( ~ r2_hidden('#skF_13',k3_relat_1('#skF_15'))
    | r2_hidden('#skF_13',k1_wellord1('#skF_15','#skF_13'))
    | ~ r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13')) ),
    inference(resolution,[status(thm)],[c_16212,c_18878])).

tff(c_18915,plain,
    ( r2_hidden('#skF_13',k1_wellord1('#skF_15','#skF_13'))
    | ~ r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_18895])).

tff(c_18922,plain,(
    ~ r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_18915])).

tff(c_15892,plain,(
    ! [B_1095] :
      ( r2_hidden(B_1095,k1_wellord1('#skF_15','#skF_14'))
      | B_1095 = '#skF_14'
      | ~ v1_relat_1('#skF_15')
      | ~ r2_hidden(k4_tarski(B_1095,'#skF_13'),'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_15887,c_12])).

tff(c_16070,plain,(
    ! [B_1101] :
      ( r2_hidden(B_1101,k1_wellord1('#skF_15','#skF_14'))
      | B_1101 = '#skF_14'
      | ~ r2_hidden(k4_tarski(B_1101,'#skF_13'),'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15892])).

tff(c_16082,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,k1_wellord1('#skF_15','#skF_14'))
      | D_20 = '#skF_14'
      | ~ r2_hidden(D_20,k1_wellord1('#skF_15','#skF_13'))
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_14,c_16070])).

tff(c_16093,plain,(
    ! [D_1102] :
      ( r2_hidden(D_1102,k1_wellord1('#skF_15','#skF_14'))
      | D_1102 = '#skF_14'
      | ~ r2_hidden(D_1102,k1_wellord1('#skF_15','#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_16082])).

tff(c_30156,plain,(
    ! [A_1666] :
      ( r1_tarski(A_1666,k1_wellord1('#skF_15','#skF_14'))
      | '#skF_1'(A_1666,k1_wellord1('#skF_15','#skF_14')) = '#skF_14'
      | ~ r2_hidden('#skF_1'(A_1666,k1_wellord1('#skF_15','#skF_14')),k1_wellord1('#skF_15','#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_16093,c_4])).

tff(c_30180,plain,
    ( '#skF_1'(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14')) = '#skF_14'
    | r1_tarski(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14')) ),
    inference(resolution,[status(thm)],[c_6,c_30156])).

tff(c_30188,plain,(
    '#skF_1'(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14')) = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_14977,c_14977,c_30180])).

tff(c_30249,plain,
    ( r2_hidden('#skF_14',k1_wellord1('#skF_15','#skF_13'))
    | r1_tarski(k1_wellord1('#skF_15','#skF_13'),k1_wellord1('#skF_15','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30188,c_6])).

tff(c_30298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14977,c_18922,c_30249])).

tff(c_30299,plain,(
    r2_hidden('#skF_13',k1_wellord1('#skF_15','#skF_13')) ),
    inference(splitRight,[status(thm)],[c_18915])).

tff(c_30320,plain,(
    ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_30299,c_16])).

tff(c_30338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_30320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:12:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.98/6.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.98/6.93  
% 15.98/6.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.98/6.93  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_9 > #skF_7 > #skF_5 > #skF_11 > #skF_4 > #skF_15 > #skF_8 > #skF_12 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_1 > #skF_6
% 15.98/6.93  
% 15.98/6.93  %Foreground sorts:
% 15.98/6.93  
% 15.98/6.93  
% 15.98/6.93  %Background operators:
% 15.98/6.93  
% 15.98/6.93  
% 15.98/6.93  %Foreground operators:
% 15.98/6.93  tff('#skF_9', type, '#skF_9': $i > $i).
% 15.98/6.93  tff('#skF_7', type, '#skF_7': $i > $i).
% 15.98/6.93  tff('#skF_5', type, '#skF_5': $i > $i).
% 15.98/6.93  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 15.98/6.93  tff('#skF_4', type, '#skF_4': $i > $i).
% 15.98/6.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.98/6.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.98/6.93  tff('#skF_15', type, '#skF_15': $i).
% 15.98/6.93  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.98/6.93  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 15.98/6.93  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 15.98/6.93  tff('#skF_8', type, '#skF_8': $i > $i).
% 15.98/6.93  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 15.98/6.93  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 15.98/6.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.98/6.94  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 15.98/6.94  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 15.98/6.94  tff('#skF_14', type, '#skF_14': $i).
% 15.98/6.94  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 15.98/6.94  tff('#skF_13', type, '#skF_13': $i).
% 15.98/6.94  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 15.98/6.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.98/6.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.98/6.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.98/6.94  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 15.98/6.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.98/6.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.98/6.94  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 15.98/6.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.98/6.94  tff('#skF_6', type, '#skF_6': $i > $i).
% 15.98/6.94  
% 15.98/6.95  tff(f_143, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 15.98/6.95  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 15.98/6.95  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 15.98/6.95  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 15.98/6.95  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 15.98/6.95  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 15.98/6.95  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> (![B, C, D]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, D), A)) => r2_hidden(k4_tarski(B, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_wellord1)).
% 15.98/6.95  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 15.98/6.95  tff(f_130, axiom, (![A, B]: (v1_relat_1(B) => ((v2_wellord1(B) & r1_tarski(A, k3_relat_1(B))) => (~(~(A = k3_relat_1(B)) & (![C]: ~(r2_hidden(C, k3_relat_1(B)) & (A = k1_wellord1(B, C))))) <=> (![C]: (r2_hidden(C, A) => (![D]: (r2_hidden(k4_tarski(D, C), B) => r2_hidden(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 15.98/6.95  tff(c_90, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.98/6.95  tff(c_88, plain, (v2_wellord1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.98/6.95  tff(c_106, plain, (![A_59]: (v1_relat_2(A_59) | ~v2_wellord1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.98/6.95  tff(c_109, plain, (v1_relat_2('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_88, c_106])).
% 15.98/6.95  tff(c_112, plain, (v1_relat_2('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_109])).
% 15.98/6.95  tff(c_86, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_15'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.98/6.95  tff(c_42, plain, (![B_25, A_22]: (r2_hidden(k4_tarski(B_25, B_25), A_22) | ~r2_hidden(B_25, k3_relat_1(A_22)) | ~v1_relat_2(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.98/6.95  tff(c_98, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_14'), '#skF_15') | r1_tarski(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.98/6.95  tff(c_114, plain, (r1_tarski(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14'))), inference(splitLeft, [status(thm)], [c_98])).
% 15.98/6.95  tff(c_34, plain, (![A_21]: (v6_relat_2(A_21) | ~v2_wellord1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.98/6.95  tff(c_84, plain, (r2_hidden('#skF_14', k3_relat_1('#skF_15'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.98/6.95  tff(c_1412, plain, (![C_267, B_268, A_269]: (r2_hidden(k4_tarski(C_267, B_268), A_269) | r2_hidden(k4_tarski(B_268, C_267), A_269) | C_267=B_268 | ~r2_hidden(C_267, k3_relat_1(A_269)) | ~r2_hidden(B_268, k3_relat_1(A_269)) | ~v6_relat_2(A_269) | ~v1_relat_1(A_269))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.98/6.95  tff(c_12, plain, (![D_20, A_9, B_16]: (r2_hidden(D_20, k1_wellord1(A_9, B_16)) | ~r2_hidden(k4_tarski(D_20, B_16), A_9) | D_20=B_16 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.98/6.95  tff(c_14638, plain, (![C_941, A_942, B_943]: (r2_hidden(C_941, k1_wellord1(A_942, B_943)) | r2_hidden(k4_tarski(B_943, C_941), A_942) | C_941=B_943 | ~r2_hidden(C_941, k3_relat_1(A_942)) | ~r2_hidden(B_943, k3_relat_1(A_942)) | ~v6_relat_2(A_942) | ~v1_relat_1(A_942))), inference(resolution, [status(thm)], [c_1412, c_12])).
% 15.98/6.95  tff(c_92, plain, (~r1_tarski(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14')) | ~r2_hidden(k4_tarski('#skF_13', '#skF_14'), '#skF_15')), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.98/6.95  tff(c_129, plain, (~r2_hidden(k4_tarski('#skF_13', '#skF_14'), '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_92])).
% 15.98/6.95  tff(c_14703, plain, (r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13')) | '#skF_14'='#skF_13' | ~r2_hidden('#skF_14', k3_relat_1('#skF_15')) | ~r2_hidden('#skF_13', k3_relat_1('#skF_15')) | ~v6_relat_2('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_14638, c_129])).
% 15.98/6.95  tff(c_14730, plain, (r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13')) | '#skF_14'='#skF_13' | ~v6_relat_2('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_14703])).
% 15.98/6.95  tff(c_14732, plain, (~v6_relat_2('#skF_15')), inference(splitLeft, [status(thm)], [c_14730])).
% 15.98/6.95  tff(c_14738, plain, (~v2_wellord1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_34, c_14732])).
% 15.98/6.95  tff(c_14745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_14738])).
% 15.98/6.95  tff(c_14746, plain, ('#skF_14'='#skF_13' | r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13'))), inference(splitRight, [status(thm)], [c_14730])).
% 15.98/6.95  tff(c_14748, plain, (r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13'))), inference(splitLeft, [status(thm)], [c_14746])).
% 15.98/6.95  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.98/6.95  tff(c_14770, plain, (![B_944]: (r2_hidden('#skF_14', B_944) | ~r1_tarski(k1_wellord1('#skF_15', '#skF_13'), B_944))), inference(resolution, [status(thm)], [c_14748, c_2])).
% 15.98/6.95  tff(c_14840, plain, (r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_14'))), inference(resolution, [status(thm)], [c_114, c_14770])).
% 15.98/6.95  tff(c_16, plain, (![D_20, A_9]: (~r2_hidden(D_20, k1_wellord1(A_9, D_20)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.98/6.95  tff(c_14852, plain, (~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_14840, c_16])).
% 15.98/6.95  tff(c_14868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_14852])).
% 15.98/6.95  tff(c_14869, plain, ('#skF_14'='#skF_13'), inference(splitRight, [status(thm)], [c_14746])).
% 15.98/6.95  tff(c_14940, plain, (~r2_hidden(k4_tarski('#skF_13', '#skF_13'), '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_14869, c_129])).
% 15.98/6.95  tff(c_14961, plain, (~r2_hidden('#skF_13', k3_relat_1('#skF_15')) | ~v1_relat_2('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_42, c_14940])).
% 15.98/6.95  tff(c_14973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_112, c_86, c_14961])).
% 15.98/6.95  tff(c_14974, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_14'), '#skF_15')), inference(splitRight, [status(thm)], [c_98])).
% 15.98/6.95  tff(c_14977, plain, (~r1_tarski(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_14974, c_92])).
% 15.98/6.95  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.98/6.95  tff(c_14, plain, (![D_20, B_16, A_9]: (r2_hidden(k4_tarski(D_20, B_16), A_9) | ~r2_hidden(D_20, k1_wellord1(A_9, B_16)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.98/6.95  tff(c_38, plain, (![A_21]: (v8_relat_2(A_21) | ~v2_wellord1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.98/6.95  tff(c_15799, plain, (![B_1089, D_1090, A_1091, C_1092]: (r2_hidden(k4_tarski(B_1089, D_1090), A_1091) | ~r2_hidden(k4_tarski(C_1092, D_1090), A_1091) | ~r2_hidden(k4_tarski(B_1089, C_1092), A_1091) | ~v8_relat_2(A_1091) | ~v1_relat_1(A_1091))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.98/6.95  tff(c_15824, plain, (![B_1089]: (r2_hidden(k4_tarski(B_1089, '#skF_14'), '#skF_15') | ~r2_hidden(k4_tarski(B_1089, '#skF_13'), '#skF_15') | ~v8_relat_2('#skF_15') | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_14974, c_15799])).
% 15.98/6.95  tff(c_15837, plain, (![B_1089]: (r2_hidden(k4_tarski(B_1089, '#skF_14'), '#skF_15') | ~r2_hidden(k4_tarski(B_1089, '#skF_13'), '#skF_15') | ~v8_relat_2('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15824])).
% 15.98/6.95  tff(c_15838, plain, (~v8_relat_2('#skF_15')), inference(splitLeft, [status(thm)], [c_15837])).
% 15.98/6.95  tff(c_15841, plain, (~v2_wellord1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_38, c_15838])).
% 15.98/6.95  tff(c_15845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_15841])).
% 15.98/6.95  tff(c_15887, plain, (![B_1095]: (r2_hidden(k4_tarski(B_1095, '#skF_14'), '#skF_15') | ~r2_hidden(k4_tarski(B_1095, '#skF_13'), '#skF_15'))), inference(splitRight, [status(thm)], [c_15837])).
% 15.98/6.95  tff(c_10, plain, (![A_6, C_8, B_7]: (r2_hidden(A_6, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.98/6.95  tff(c_15898, plain, (![B_1095]: (r2_hidden(B_1095, k3_relat_1('#skF_15')) | ~v1_relat_1('#skF_15') | ~r2_hidden(k4_tarski(B_1095, '#skF_13'), '#skF_15'))), inference(resolution, [status(thm)], [c_15887, c_10])).
% 15.98/6.95  tff(c_15914, plain, (![B_1096]: (r2_hidden(B_1096, k3_relat_1('#skF_15')) | ~r2_hidden(k4_tarski(B_1096, '#skF_13'), '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15898])).
% 15.98/6.95  tff(c_15922, plain, (![D_20]: (r2_hidden(D_20, k3_relat_1('#skF_15')) | ~r2_hidden(D_20, k1_wellord1('#skF_15', '#skF_13')) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_14, c_15914])).
% 15.98/6.95  tff(c_15929, plain, (![D_1097]: (r2_hidden(D_1097, k3_relat_1('#skF_15')) | ~r2_hidden(D_1097, k1_wellord1('#skF_15', '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15922])).
% 15.98/6.95  tff(c_16204, plain, (![B_1108]: (r2_hidden('#skF_1'(k1_wellord1('#skF_15', '#skF_13'), B_1108), k3_relat_1('#skF_15')) | r1_tarski(k1_wellord1('#skF_15', '#skF_13'), B_1108))), inference(resolution, [status(thm)], [c_6, c_15929])).
% 15.98/6.95  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.98/6.95  tff(c_16212, plain, (r1_tarski(k1_wellord1('#skF_15', '#skF_13'), k3_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_16204, c_4])).
% 15.98/6.95  tff(c_18742, plain, (![C_1296, B_1297, D_1298, C_1299]: (~r2_hidden(C_1296, k3_relat_1(B_1297)) | r2_hidden(D_1298, k1_wellord1(B_1297, C_1296)) | ~r2_hidden(k4_tarski(D_1298, C_1299), B_1297) | ~r2_hidden(C_1299, k1_wellord1(B_1297, C_1296)) | ~r1_tarski(k1_wellord1(B_1297, C_1296), k3_relat_1(B_1297)) | ~v2_wellord1(B_1297) | ~v1_relat_1(B_1297))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.98/6.95  tff(c_18795, plain, (![C_1296]: (~r2_hidden(C_1296, k3_relat_1('#skF_15')) | r2_hidden('#skF_13', k1_wellord1('#skF_15', C_1296)) | ~r2_hidden('#skF_14', k1_wellord1('#skF_15', C_1296)) | ~r1_tarski(k1_wellord1('#skF_15', C_1296), k3_relat_1('#skF_15')) | ~v2_wellord1('#skF_15') | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_14974, c_18742])).
% 15.98/6.95  tff(c_18878, plain, (![C_1304]: (~r2_hidden(C_1304, k3_relat_1('#skF_15')) | r2_hidden('#skF_13', k1_wellord1('#skF_15', C_1304)) | ~r2_hidden('#skF_14', k1_wellord1('#skF_15', C_1304)) | ~r1_tarski(k1_wellord1('#skF_15', C_1304), k3_relat_1('#skF_15')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_18795])).
% 15.98/6.95  tff(c_18895, plain, (~r2_hidden('#skF_13', k3_relat_1('#skF_15')) | r2_hidden('#skF_13', k1_wellord1('#skF_15', '#skF_13')) | ~r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13'))), inference(resolution, [status(thm)], [c_16212, c_18878])).
% 15.98/6.95  tff(c_18915, plain, (r2_hidden('#skF_13', k1_wellord1('#skF_15', '#skF_13')) | ~r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_18895])).
% 15.98/6.95  tff(c_18922, plain, (~r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13'))), inference(splitLeft, [status(thm)], [c_18915])).
% 15.98/6.95  tff(c_15892, plain, (![B_1095]: (r2_hidden(B_1095, k1_wellord1('#skF_15', '#skF_14')) | B_1095='#skF_14' | ~v1_relat_1('#skF_15') | ~r2_hidden(k4_tarski(B_1095, '#skF_13'), '#skF_15'))), inference(resolution, [status(thm)], [c_15887, c_12])).
% 15.98/6.95  tff(c_16070, plain, (![B_1101]: (r2_hidden(B_1101, k1_wellord1('#skF_15', '#skF_14')) | B_1101='#skF_14' | ~r2_hidden(k4_tarski(B_1101, '#skF_13'), '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15892])).
% 15.98/6.95  tff(c_16082, plain, (![D_20]: (r2_hidden(D_20, k1_wellord1('#skF_15', '#skF_14')) | D_20='#skF_14' | ~r2_hidden(D_20, k1_wellord1('#skF_15', '#skF_13')) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_14, c_16070])).
% 15.98/6.95  tff(c_16093, plain, (![D_1102]: (r2_hidden(D_1102, k1_wellord1('#skF_15', '#skF_14')) | D_1102='#skF_14' | ~r2_hidden(D_1102, k1_wellord1('#skF_15', '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_16082])).
% 15.98/6.95  tff(c_30156, plain, (![A_1666]: (r1_tarski(A_1666, k1_wellord1('#skF_15', '#skF_14')) | '#skF_1'(A_1666, k1_wellord1('#skF_15', '#skF_14'))='#skF_14' | ~r2_hidden('#skF_1'(A_1666, k1_wellord1('#skF_15', '#skF_14')), k1_wellord1('#skF_15', '#skF_13')))), inference(resolution, [status(thm)], [c_16093, c_4])).
% 15.98/6.95  tff(c_30180, plain, ('#skF_1'(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14'))='#skF_14' | r1_tarski(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14'))), inference(resolution, [status(thm)], [c_6, c_30156])).
% 15.98/6.95  tff(c_30188, plain, ('#skF_1'(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14'))='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_14977, c_14977, c_30180])).
% 15.98/6.95  tff(c_30249, plain, (r2_hidden('#skF_14', k1_wellord1('#skF_15', '#skF_13')) | r1_tarski(k1_wellord1('#skF_15', '#skF_13'), k1_wellord1('#skF_15', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_30188, c_6])).
% 15.98/6.95  tff(c_30298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14977, c_18922, c_30249])).
% 15.98/6.95  tff(c_30299, plain, (r2_hidden('#skF_13', k1_wellord1('#skF_15', '#skF_13'))), inference(splitRight, [status(thm)], [c_18915])).
% 15.98/6.95  tff(c_30320, plain, (~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_30299, c_16])).
% 15.98/6.95  tff(c_30338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_30320])).
% 15.98/6.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.98/6.95  
% 15.98/6.95  Inference rules
% 15.98/6.95  ----------------------
% 15.98/6.95  #Ref     : 0
% 15.98/6.95  #Sup     : 6951
% 15.98/6.95  #Fact    : 10
% 15.98/6.95  #Define  : 0
% 15.98/6.95  #Split   : 36
% 15.98/6.95  #Chain   : 0
% 15.98/6.95  #Close   : 0
% 15.98/6.95  
% 15.98/6.95  Ordering : KBO
% 15.98/6.95  
% 15.98/6.95  Simplification rules
% 15.98/6.95  ----------------------
% 15.98/6.95  #Subsume      : 3145
% 15.98/6.95  #Demod        : 1525
% 15.98/6.95  #Tautology    : 457
% 15.98/6.95  #SimpNegUnit  : 74
% 15.98/6.95  #BackRed      : 200
% 15.98/6.95  
% 15.98/6.95  #Partial instantiations: 0
% 15.98/6.95  #Strategies tried      : 1
% 15.98/6.95  
% 15.98/6.95  Timing (in seconds)
% 15.98/6.95  ----------------------
% 15.98/6.95  Preprocessing        : 0.34
% 15.98/6.95  Parsing              : 0.17
% 15.98/6.95  CNF conversion       : 0.03
% 15.98/6.95  Main loop            : 5.86
% 15.98/6.95  Inferencing          : 1.39
% 15.98/6.95  Reduction            : 1.23
% 15.98/6.95  Demodulation         : 0.82
% 15.98/6.95  BG Simplification    : 0.16
% 15.98/6.95  Subsumption          : 2.69
% 15.98/6.96  Abstraction          : 0.21
% 15.98/6.96  MUC search           : 0.00
% 15.98/6.96  Cooper               : 0.00
% 15.98/6.96  Total                : 6.24
% 15.98/6.96  Index Insertion      : 0.00
% 15.98/6.96  Index Deletion       : 0.00
% 15.98/6.96  Index Matching       : 0.00
% 15.98/6.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
