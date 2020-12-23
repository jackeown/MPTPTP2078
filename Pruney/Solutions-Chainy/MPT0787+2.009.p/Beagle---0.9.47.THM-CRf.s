%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:46 EST 2020

% Result     : Theorem 32.62s
% Output     : CNFRefutation 32.66s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 692 expanded)
%              Number of leaves         :   40 ( 249 expanded)
%              Depth                    :   15
%              Number of atoms          :  344 (2207 expanded)
%              Number of equality atoms :   32 ( 143 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_11 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r2_hidden(k4_tarski(A,B),C)
          <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_126,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => ? [C] :
        ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,k3_relat_1(A))
            & ~ r2_hidden(k4_tarski(D,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( r2_hidden(D,B)
                       => r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_91,axiom,(
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

tff(f_150,axiom,(
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
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_98,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_13')
    | r1_tarski(k1_wellord1('#skF_13','#skF_11'),k1_wellord1('#skF_13','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_115,plain,(
    r1_tarski(k1_wellord1('#skF_13','#skF_11'),k1_wellord1('#skF_13','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_88,plain,(
    v2_wellord1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_132,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84),A_83)
      | r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_83] : r1_tarski(A_83,A_83) ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_66,plain,(
    ! [B_53,A_52] :
      ( r1_tarski(k1_wellord1(B_53,A_52),k3_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_188,plain,(
    ! [D_101,A_102,B_103] :
      ( r2_hidden(D_101,k3_relat_1(A_102))
      | ~ r2_hidden(D_101,'#skF_6'(A_102,B_103))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2962,plain,(
    ! [A_314,B_315,B_316] :
      ( r2_hidden('#skF_1'('#skF_6'(A_314,B_315),B_316),k3_relat_1(A_314))
      | ~ v1_relat_1(A_314)
      | r1_tarski('#skF_6'(A_314,B_315),B_316) ) ),
    inference(resolution,[status(thm)],[c_6,c_188])).

tff(c_2976,plain,(
    ! [A_314,B_315] :
      ( ~ v1_relat_1(A_314)
      | r1_tarski('#skF_6'(A_314,B_315),k3_relat_1(A_314)) ) ),
    inference(resolution,[status(thm)],[c_2962,c_4])).

tff(c_224,plain,(
    ! [D_117,B_118,A_119] :
      ( r2_hidden(k4_tarski(D_117,B_118),A_119)
      | ~ r2_hidden(D_117,k1_wellord1(A_119,B_118))
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_7,C_8,A_6] :
      ( r2_hidden(B_7,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_270,plain,(
    ! [B_121,A_122,D_123] :
      ( r2_hidden(B_121,k3_relat_1(A_122))
      | ~ r2_hidden(D_123,k1_wellord1(A_122,B_121))
      | ~ v1_relat_1(A_122) ) ),
    inference(resolution,[status(thm)],[c_224,c_8])).

tff(c_282,plain,(
    ! [B_121,A_122,B_2] :
      ( r2_hidden(B_121,k3_relat_1(A_122))
      | ~ v1_relat_1(A_122)
      | r1_tarski(k1_wellord1(A_122,B_121),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_270])).

tff(c_558,plain,(
    ! [D_159,A_160,B_161] :
      ( r2_hidden(D_159,'#skF_6'(A_160,B_161))
      | r2_hidden(k4_tarski(D_159,B_161),A_160)
      | ~ r2_hidden(D_159,k3_relat_1(A_160))
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_885,plain,(
    ! [B_202,A_203,D_204] :
      ( r2_hidden(B_202,k3_relat_1(A_203))
      | r2_hidden(D_204,'#skF_6'(A_203,B_202))
      | ~ r2_hidden(D_204,k3_relat_1(A_203))
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_558,c_8])).

tff(c_4171,plain,(
    ! [B_430,A_431,B_432,B_433] :
      ( r2_hidden(B_430,k3_relat_1(A_431))
      | r2_hidden(B_432,'#skF_6'(A_431,B_430))
      | ~ v1_relat_1(A_431)
      | r1_tarski(k1_wellord1(A_431,B_432),B_433) ) ),
    inference(resolution,[status(thm)],[c_282,c_885])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4713,plain,(
    ! [A_444,B_445,B_446,B_447] :
      ( ~ r1_tarski('#skF_6'(A_444,B_445),B_446)
      | r2_hidden(B_445,k3_relat_1(A_444))
      | ~ v1_relat_1(A_444)
      | r1_tarski(k1_wellord1(A_444,B_446),B_447) ) ),
    inference(resolution,[status(thm)],[c_4171,c_12])).

tff(c_4721,plain,(
    ! [B_448,A_449,B_450] :
      ( r2_hidden(B_448,k3_relat_1(A_449))
      | r1_tarski(k1_wellord1(A_449,k3_relat_1(A_449)),B_450)
      | ~ v1_relat_1(A_449) ) ),
    inference(resolution,[status(thm)],[c_2976,c_4713])).

tff(c_5072,plain,(
    ! [A_455,B_456,B_457] :
      ( ~ r1_tarski(k3_relat_1(A_455),B_456)
      | r1_tarski(k1_wellord1(A_455,k3_relat_1(A_455)),B_457)
      | ~ v1_relat_1(A_455) ) ),
    inference(resolution,[status(thm)],[c_4721,c_12])).

tff(c_5079,plain,(
    ! [A_458,B_459] :
      ( r1_tarski(k1_wellord1(A_458,k3_relat_1(A_458)),B_459)
      | ~ v1_relat_1(A_458) ) ),
    inference(resolution,[status(thm)],[c_140,c_5072])).

tff(c_490,plain,(
    ! [A_150,B_151] :
      ( r2_hidden('#skF_7'(A_150,B_151),B_151)
      | k1_xboole_0 = B_151
      | ~ r1_tarski(B_151,k3_relat_1(A_150))
      | ~ v2_wellord1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_520,plain,(
    ! [B_151,A_150] :
      ( ~ r1_tarski(B_151,'#skF_7'(A_150,B_151))
      | k1_xboole_0 = B_151
      | ~ r1_tarski(B_151,k3_relat_1(A_150))
      | ~ v2_wellord1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_490,c_12])).

tff(c_27079,plain,(
    ! [A_1180,A_1181] :
      ( k1_wellord1(A_1180,k3_relat_1(A_1180)) = k1_xboole_0
      | ~ r1_tarski(k1_wellord1(A_1180,k3_relat_1(A_1180)),k3_relat_1(A_1181))
      | ~ v2_wellord1(A_1181)
      | ~ v1_relat_1(A_1181)
      | ~ v1_relat_1(A_1180) ) ),
    inference(resolution,[status(thm)],[c_5079,c_520])).

tff(c_27160,plain,(
    ! [B_1182] :
      ( k1_wellord1(B_1182,k3_relat_1(B_1182)) = k1_xboole_0
      | ~ v2_wellord1(B_1182)
      | ~ v1_relat_1(B_1182) ) ),
    inference(resolution,[status(thm)],[c_66,c_27079])).

tff(c_305,plain,(
    ! [B_129,A_130,B_131] :
      ( r2_hidden(B_129,k3_relat_1(A_130))
      | ~ v1_relat_1(A_130)
      | r1_tarski(k1_wellord1(A_130,B_129),B_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_270])).

tff(c_350,plain,(
    ! [A_130,B_129,B_131] :
      ( ~ r1_tarski(k3_relat_1(A_130),B_129)
      | ~ v1_relat_1(A_130)
      | r1_tarski(k1_wellord1(A_130,B_129),B_131) ) ),
    inference(resolution,[status(thm)],[c_305,c_12])).

tff(c_27347,plain,(
    ! [B_1182,B_131] :
      ( ~ r1_tarski(k3_relat_1(B_1182),k3_relat_1(B_1182))
      | ~ v1_relat_1(B_1182)
      | r1_tarski(k1_xboole_0,B_131)
      | ~ v2_wellord1(B_1182)
      | ~ v1_relat_1(B_1182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27160,c_350])).

tff(c_27422,plain,(
    ! [B_131,B_1182] :
      ( r1_tarski(k1_xboole_0,B_131)
      | ~ v2_wellord1(B_1182)
      | ~ v1_relat_1(B_1182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_27347])).

tff(c_27425,plain,(
    ! [B_1183] :
      ( ~ v2_wellord1(B_1183)
      | ~ v1_relat_1(B_1183) ) ),
    inference(splitLeft,[status(thm)],[c_27422])).

tff(c_27428,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_88,c_27425])).

tff(c_27432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_27428])).

tff(c_27433,plain,(
    ! [B_131] : r1_tarski(k1_xboole_0,B_131) ),
    inference(splitRight,[status(thm)],[c_27422])).

tff(c_36,plain,(
    ! [A_23] :
      ( v6_relat_2(A_23)
      | ~ v2_wellord1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    r2_hidden('#skF_12',k3_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_86,plain,(
    r2_hidden('#skF_11',k3_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2502,plain,(
    ! [C_289,B_290,A_291] :
      ( r2_hidden(k4_tarski(C_289,B_290),A_291)
      | r2_hidden(k4_tarski(B_290,C_289),A_291)
      | C_289 = B_290
      | ~ r2_hidden(C_289,k3_relat_1(A_291))
      | ~ r2_hidden(B_290,k3_relat_1(A_291))
      | ~ v6_relat_2(A_291)
      | ~ v1_relat_1(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_92,plain,
    ( ~ r1_tarski(k1_wellord1('#skF_13','#skF_11'),k1_wellord1('#skF_13','#skF_12'))
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_130,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_92])).

tff(c_2546,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_13')
    | '#skF_11' = '#skF_12'
    | ~ r2_hidden('#skF_11',k3_relat_1('#skF_13'))
    | ~ r2_hidden('#skF_12',k3_relat_1('#skF_13'))
    | ~ v6_relat_2('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_2502,c_130])).

tff(c_2619,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_13')
    | '#skF_11' = '#skF_12'
    | ~ v6_relat_2('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_84,c_86,c_2546])).

tff(c_2639,plain,(
    ~ v6_relat_2('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_2619])).

tff(c_2645,plain,
    ( ~ v2_wellord1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_36,c_2639])).

tff(c_2652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_2645])).

tff(c_2654,plain,(
    v6_relat_2('#skF_13') ),
    inference(splitRight,[status(thm)],[c_2619])).

tff(c_2597,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_13')
    | '#skF_11' = '#skF_12'
    | ~ r2_hidden('#skF_12',k3_relat_1('#skF_13'))
    | ~ r2_hidden('#skF_11',k3_relat_1('#skF_13'))
    | ~ v6_relat_2('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_2502,c_130])).

tff(c_2636,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_13')
    | '#skF_11' = '#skF_12'
    | ~ v6_relat_2('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_2597])).

tff(c_2656,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_13')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_2636])).

tff(c_2657,plain,(
    '#skF_11' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_2656])).

tff(c_601,plain,
    ( r2_hidden('#skF_11','#skF_6'('#skF_13','#skF_12'))
    | ~ r2_hidden('#skF_11',k3_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_558,c_130])).

tff(c_623,plain,(
    r2_hidden('#skF_11','#skF_6'('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_601])).

tff(c_2689,plain,(
    r2_hidden('#skF_12','#skF_6'('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_623])).

tff(c_64,plain,(
    ! [A_38,B_46] :
      ( r2_hidden('#skF_7'(A_38,B_46),B_46)
      | k1_xboole_0 = B_46
      | ~ r1_tarski(B_46,k3_relat_1(A_38))
      | ~ v2_wellord1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1305,plain,(
    ! [A_220,B_221,D_222] :
      ( r2_hidden(k4_tarski('#skF_7'(A_220,B_221),D_222),A_220)
      | ~ r2_hidden(D_222,B_221)
      | k1_xboole_0 = B_221
      | ~ r1_tarski(B_221,k3_relat_1(A_220))
      | ~ v2_wellord1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    ! [D_37,B_32,A_31] :
      ( ~ r2_hidden(k4_tarski(D_37,B_32),A_31)
      | ~ r2_hidden(D_37,'#skF_6'(A_31,B_32))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10067,plain,(
    ! [A_680,B_681,D_682] :
      ( ~ r2_hidden('#skF_7'(A_680,B_681),'#skF_6'(A_680,D_682))
      | ~ r2_hidden(D_682,B_681)
      | k1_xboole_0 = B_681
      | ~ r1_tarski(B_681,k3_relat_1(A_680))
      | ~ v2_wellord1(A_680)
      | ~ v1_relat_1(A_680) ) ),
    inference(resolution,[status(thm)],[c_1305,c_58])).

tff(c_72382,plain,(
    ! [D_1769,A_1770] :
      ( ~ r2_hidden(D_1769,'#skF_6'(A_1770,D_1769))
      | '#skF_6'(A_1770,D_1769) = k1_xboole_0
      | ~ r1_tarski('#skF_6'(A_1770,D_1769),k3_relat_1(A_1770))
      | ~ v2_wellord1(A_1770)
      | ~ v1_relat_1(A_1770) ) ),
    inference(resolution,[status(thm)],[c_64,c_10067])).

tff(c_72636,plain,
    ( '#skF_6'('#skF_13','#skF_12') = k1_xboole_0
    | ~ r1_tarski('#skF_6'('#skF_13','#skF_12'),k3_relat_1('#skF_13'))
    | ~ v2_wellord1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_2689,c_72382])).

tff(c_72863,plain,
    ( '#skF_6'('#skF_13','#skF_12') = k1_xboole_0
    | ~ r1_tarski('#skF_6'('#skF_13','#skF_12'),k3_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_72636])).

tff(c_72894,plain,(
    ~ r1_tarski('#skF_6'('#skF_13','#skF_12'),k3_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_72863])).

tff(c_72898,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_2976,c_72894])).

tff(c_72902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_72898])).

tff(c_72903,plain,(
    '#skF_6'('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72863])).

tff(c_144,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_195,plain,(
    ! [A_108,B_109,B_110] :
      ( r2_hidden('#skF_1'(A_108,B_109),B_110)
      | ~ r1_tarski(A_108,B_110)
      | r1_tarski(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_678,plain,(
    ! [A_170,B_171,B_172,B_173] :
      ( r2_hidden('#skF_1'(A_170,B_171),B_172)
      | ~ r1_tarski(B_173,B_172)
      | ~ r1_tarski(A_170,B_173)
      | r1_tarski(A_170,B_171) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_712,plain,(
    ! [A_178,B_179] :
      ( r2_hidden('#skF_1'(A_178,B_179),k1_wellord1('#skF_13','#skF_12'))
      | ~ r1_tarski(A_178,k1_wellord1('#skF_13','#skF_11'))
      | r1_tarski(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_115,c_678])).

tff(c_257,plain,(
    ! [D_117,A_119,B_118] :
      ( ~ r2_hidden(D_117,'#skF_6'(A_119,B_118))
      | ~ r2_hidden(D_117,k1_wellord1(A_119,B_118))
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_224,c_58])).

tff(c_715,plain,(
    ! [A_178,B_179] :
      ( ~ r2_hidden('#skF_1'(A_178,B_179),'#skF_6'('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13')
      | ~ r1_tarski(A_178,k1_wellord1('#skF_13','#skF_11'))
      | r1_tarski(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_712,c_257])).

tff(c_735,plain,(
    ! [A_178,B_179] :
      ( ~ r2_hidden('#skF_1'(A_178,B_179),'#skF_6'('#skF_13','#skF_12'))
      | ~ r1_tarski(A_178,k1_wellord1('#skF_13','#skF_11'))
      | r1_tarski(A_178,B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_715])).

tff(c_3290,plain,(
    ! [A_348,B_349] :
      ( ~ r2_hidden('#skF_1'(A_348,B_349),'#skF_6'('#skF_13','#skF_12'))
      | ~ r1_tarski(A_348,k1_wellord1('#skF_13','#skF_12'))
      | r1_tarski(A_348,B_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_735])).

tff(c_3318,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_6'('#skF_13','#skF_12'),k1_wellord1('#skF_13','#skF_12'))
      | r1_tarski('#skF_6'('#skF_13','#skF_12'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_3290])).

tff(c_3383,plain,(
    ~ r1_tarski('#skF_6'('#skF_13','#skF_12'),k1_wellord1('#skF_13','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_3318])).

tff(c_72908,plain,(
    ~ r1_tarski(k1_xboole_0,k1_wellord1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72903,c_3383])).

tff(c_72915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27433,c_72908])).

tff(c_72916,plain,(
    ! [B_2] : r1_tarski('#skF_6'('#skF_13','#skF_12'),B_2) ),
    inference(splitRight,[status(thm)],[c_3318])).

tff(c_637,plain,(
    ~ r1_tarski('#skF_6'('#skF_13','#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_623,c_12])).

tff(c_2688,plain,(
    ~ r1_tarski('#skF_6'('#skF_13','#skF_12'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_637])).

tff(c_72923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72916,c_2688])).

tff(c_72925,plain,(
    '#skF_11' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_2656])).

tff(c_72924,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_13') ),
    inference(splitRight,[status(thm)],[c_2656])).

tff(c_14,plain,(
    ! [D_22,A_11,B_18] :
      ( r2_hidden(D_22,k1_wellord1(A_11,B_18))
      | ~ r2_hidden(k4_tarski(D_22,B_18),A_11)
      | D_22 = B_18
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72928,plain,
    ( r2_hidden('#skF_12',k1_wellord1('#skF_13','#skF_11'))
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_72924,c_14])).

tff(c_72945,plain,
    ( r2_hidden('#skF_12',k1_wellord1('#skF_13','#skF_11'))
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_72928])).

tff(c_72946,plain,(
    r2_hidden('#skF_12',k1_wellord1('#skF_13','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_72925,c_72945])).

tff(c_73185,plain,(
    ! [B_1775] :
      ( r2_hidden('#skF_12',B_1775)
      | ~ r1_tarski(k1_wellord1('#skF_13','#skF_11'),B_1775) ) ),
    inference(resolution,[status(thm)],[c_72946,c_2])).

tff(c_73221,plain,(
    r2_hidden('#skF_12',k1_wellord1('#skF_13','#skF_12')) ),
    inference(resolution,[status(thm)],[c_115,c_73185])).

tff(c_18,plain,(
    ! [D_22,A_11] :
      ( ~ r2_hidden(D_22,k1_wellord1(A_11,D_22))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_73237,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_73221,c_18])).

tff(c_73257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_73237])).

tff(c_73258,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_13') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_73273,plain,(
    ~ r1_tarski(k1_wellord1('#skF_13','#skF_11'),k1_wellord1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73258,c_92])).

tff(c_73283,plain,(
    ! [A_1785,B_1786] :
      ( ~ r2_hidden('#skF_1'(A_1785,B_1786),B_1786)
      | r1_tarski(A_1785,B_1786) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73288,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_73283])).

tff(c_73799,plain,(
    ! [D_1870,A_1871,B_1872] :
      ( r2_hidden(D_1870,k1_wellord1(A_1871,B_1872))
      | ~ r2_hidden(k4_tarski(D_1870,B_1872),A_1871)
      | D_1870 = B_1872
      | ~ v1_relat_1(A_1871) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_73816,plain,
    ( r2_hidden('#skF_11',k1_wellord1('#skF_13','#skF_12'))
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_73258,c_73799])).

tff(c_73823,plain,
    ( r2_hidden('#skF_11',k1_wellord1('#skF_13','#skF_12'))
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_73816])).

tff(c_73824,plain,(
    '#skF_11' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_73823])).

tff(c_73836,plain,(
    ~ r1_tarski(k1_wellord1('#skF_13','#skF_12'),k1_wellord1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73824,c_73273])).

tff(c_73843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73288,c_73836])).

tff(c_73844,plain,(
    r2_hidden('#skF_11',k1_wellord1('#skF_13','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_73823])).

tff(c_16,plain,(
    ! [D_22,B_18,A_11] :
      ( r2_hidden(k4_tarski(D_22,B_18),A_11)
      | ~ r2_hidden(D_22,k1_wellord1(A_11,B_18))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77677,plain,(
    ! [C_2121,B_2122,D_2123,C_2124] :
      ( ~ r2_hidden(C_2121,k3_relat_1(B_2122))
      | r2_hidden(D_2123,k1_wellord1(B_2122,C_2121))
      | ~ r2_hidden(k4_tarski(D_2123,C_2124),B_2122)
      | ~ r2_hidden(C_2124,k1_wellord1(B_2122,C_2121))
      | ~ r1_tarski(k1_wellord1(B_2122,C_2121),k3_relat_1(B_2122))
      | ~ v2_wellord1(B_2122)
      | ~ v1_relat_1(B_2122) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_115268,plain,(
    ! [C_3412,A_3413,D_3414,B_3415] :
      ( ~ r2_hidden(C_3412,k3_relat_1(A_3413))
      | r2_hidden(D_3414,k1_wellord1(A_3413,C_3412))
      | ~ r2_hidden(B_3415,k1_wellord1(A_3413,C_3412))
      | ~ r1_tarski(k1_wellord1(A_3413,C_3412),k3_relat_1(A_3413))
      | ~ v2_wellord1(A_3413)
      | ~ r2_hidden(D_3414,k1_wellord1(A_3413,B_3415))
      | ~ v1_relat_1(A_3413) ) ),
    inference(resolution,[status(thm)],[c_16,c_77677])).

tff(c_115406,plain,(
    ! [D_3414] :
      ( ~ r2_hidden('#skF_12',k3_relat_1('#skF_13'))
      | r2_hidden(D_3414,k1_wellord1('#skF_13','#skF_12'))
      | ~ r1_tarski(k1_wellord1('#skF_13','#skF_12'),k3_relat_1('#skF_13'))
      | ~ v2_wellord1('#skF_13')
      | ~ r2_hidden(D_3414,k1_wellord1('#skF_13','#skF_11'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_73844,c_115268])).

tff(c_115467,plain,(
    ! [D_3414] :
      ( r2_hidden(D_3414,k1_wellord1('#skF_13','#skF_12'))
      | ~ r1_tarski(k1_wellord1('#skF_13','#skF_12'),k3_relat_1('#skF_13'))
      | ~ r2_hidden(D_3414,k1_wellord1('#skF_13','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_115406])).

tff(c_115475,plain,(
    ~ r1_tarski(k1_wellord1('#skF_13','#skF_12'),k3_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_115467])).

tff(c_115495,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_66,c_115475])).

tff(c_115514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_115495])).

tff(c_115672,plain,(
    ! [D_3419] :
      ( r2_hidden(D_3419,k1_wellord1('#skF_13','#skF_12'))
      | ~ r2_hidden(D_3419,k1_wellord1('#skF_13','#skF_11')) ) ),
    inference(splitRight,[status(thm)],[c_115467])).

tff(c_116102,plain,(
    ! [B_3426] :
      ( r2_hidden('#skF_1'(k1_wellord1('#skF_13','#skF_11'),B_3426),k1_wellord1('#skF_13','#skF_12'))
      | r1_tarski(k1_wellord1('#skF_13','#skF_11'),B_3426) ) ),
    inference(resolution,[status(thm)],[c_6,c_115672])).

tff(c_116121,plain,(
    r1_tarski(k1_wellord1('#skF_13','#skF_11'),k1_wellord1('#skF_13','#skF_12')) ),
    inference(resolution,[status(thm)],[c_116102,c_4])).

tff(c_116148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73273,c_73273,c_116121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.62/21.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.66/21.88  
% 32.66/21.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.66/21.89  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_11 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12
% 32.66/21.89  
% 32.66/21.89  %Foreground sorts:
% 32.66/21.89  
% 32.66/21.89  
% 32.66/21.89  %Background operators:
% 32.66/21.89  
% 32.66/21.89  
% 32.66/21.89  %Foreground operators:
% 32.66/21.89  tff('#skF_5', type, '#skF_5': $i > $i).
% 32.66/21.89  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 32.66/21.89  tff('#skF_4', type, '#skF_4': $i > $i).
% 32.66/21.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.66/21.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.66/21.89  tff('#skF_11', type, '#skF_11': $i).
% 32.66/21.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 32.66/21.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 32.66/21.89  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 32.66/21.89  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 32.66/21.89  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 32.66/21.89  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 32.66/21.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.66/21.89  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 32.66/21.89  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 32.66/21.89  tff('#skF_13', type, '#skF_13': $i).
% 32.66/21.89  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 32.66/21.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 32.66/21.89  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 32.66/21.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.66/21.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 32.66/21.89  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 32.66/21.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 32.66/21.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.66/21.89  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 32.66/21.89  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 32.66/21.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 32.66/21.89  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 32.66/21.89  tff('#skF_12', type, '#skF_12': $i).
% 32.66/21.89  
% 32.66/21.91  tff(f_163, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 32.66/21.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 32.66/21.91  tff(f_126, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_wellord1)).
% 32.66/21.91  tff(f_102, axiom, (![A, B]: (v1_relat_1(A) => (?[C]: (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k3_relat_1(A)) & ~r2_hidden(k4_tarski(D, B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e7_18__wellord1)).
% 32.66/21.91  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 32.66/21.91  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 32.66/21.91  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 32.66/21.91  tff(f_122, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~((r1_tarski(B, k3_relat_1(A)) & ~(B = k1_xboole_0)) & (![C]: ~(r2_hidden(C, B) & (![D]: (r2_hidden(D, B) => r2_hidden(k4_tarski(C, D), A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord1)).
% 32.66/21.91  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 32.66/21.91  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 32.66/21.91  tff(f_150, axiom, (![A, B]: (v1_relat_1(B) => ((v2_wellord1(B) & r1_tarski(A, k3_relat_1(B))) => (~(~(A = k3_relat_1(B)) & (![C]: ~(r2_hidden(C, k3_relat_1(B)) & (A = k1_wellord1(B, C))))) <=> (![C]: (r2_hidden(C, A) => (![D]: (r2_hidden(k4_tarski(D, C), B) => r2_hidden(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 32.66/21.91  tff(c_90, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_163])).
% 32.66/21.91  tff(c_98, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_13') | r1_tarski(k1_wellord1('#skF_13', '#skF_11'), k1_wellord1('#skF_13', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 32.66/21.91  tff(c_115, plain, (r1_tarski(k1_wellord1('#skF_13', '#skF_11'), k1_wellord1('#skF_13', '#skF_12'))), inference(splitLeft, [status(thm)], [c_98])).
% 32.66/21.91  tff(c_88, plain, (v2_wellord1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_163])).
% 32.66/21.91  tff(c_132, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84), A_83) | r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.66/21.91  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.66/21.91  tff(c_140, plain, (![A_83]: (r1_tarski(A_83, A_83))), inference(resolution, [status(thm)], [c_132, c_4])).
% 32.66/21.91  tff(c_66, plain, (![B_53, A_52]: (r1_tarski(k1_wellord1(B_53, A_52), k3_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_126])).
% 32.66/21.91  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.66/21.91  tff(c_188, plain, (![D_101, A_102, B_103]: (r2_hidden(D_101, k3_relat_1(A_102)) | ~r2_hidden(D_101, '#skF_6'(A_102, B_103)) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_102])).
% 32.66/21.91  tff(c_2962, plain, (![A_314, B_315, B_316]: (r2_hidden('#skF_1'('#skF_6'(A_314, B_315), B_316), k3_relat_1(A_314)) | ~v1_relat_1(A_314) | r1_tarski('#skF_6'(A_314, B_315), B_316))), inference(resolution, [status(thm)], [c_6, c_188])).
% 32.66/21.91  tff(c_2976, plain, (![A_314, B_315]: (~v1_relat_1(A_314) | r1_tarski('#skF_6'(A_314, B_315), k3_relat_1(A_314)))), inference(resolution, [status(thm)], [c_2962, c_4])).
% 32.66/21.91  tff(c_224, plain, (![D_117, B_118, A_119]: (r2_hidden(k4_tarski(D_117, B_118), A_119) | ~r2_hidden(D_117, k1_wellord1(A_119, B_118)) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.66/21.91  tff(c_8, plain, (![B_7, C_8, A_6]: (r2_hidden(B_7, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 32.66/21.91  tff(c_270, plain, (![B_121, A_122, D_123]: (r2_hidden(B_121, k3_relat_1(A_122)) | ~r2_hidden(D_123, k1_wellord1(A_122, B_121)) | ~v1_relat_1(A_122))), inference(resolution, [status(thm)], [c_224, c_8])).
% 32.66/21.91  tff(c_282, plain, (![B_121, A_122, B_2]: (r2_hidden(B_121, k3_relat_1(A_122)) | ~v1_relat_1(A_122) | r1_tarski(k1_wellord1(A_122, B_121), B_2))), inference(resolution, [status(thm)], [c_6, c_270])).
% 32.66/21.91  tff(c_558, plain, (![D_159, A_160, B_161]: (r2_hidden(D_159, '#skF_6'(A_160, B_161)) | r2_hidden(k4_tarski(D_159, B_161), A_160) | ~r2_hidden(D_159, k3_relat_1(A_160)) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_102])).
% 32.66/21.91  tff(c_885, plain, (![B_202, A_203, D_204]: (r2_hidden(B_202, k3_relat_1(A_203)) | r2_hidden(D_204, '#skF_6'(A_203, B_202)) | ~r2_hidden(D_204, k3_relat_1(A_203)) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_558, c_8])).
% 32.66/21.91  tff(c_4171, plain, (![B_430, A_431, B_432, B_433]: (r2_hidden(B_430, k3_relat_1(A_431)) | r2_hidden(B_432, '#skF_6'(A_431, B_430)) | ~v1_relat_1(A_431) | r1_tarski(k1_wellord1(A_431, B_432), B_433))), inference(resolution, [status(thm)], [c_282, c_885])).
% 32.66/21.91  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 32.66/21.91  tff(c_4713, plain, (![A_444, B_445, B_446, B_447]: (~r1_tarski('#skF_6'(A_444, B_445), B_446) | r2_hidden(B_445, k3_relat_1(A_444)) | ~v1_relat_1(A_444) | r1_tarski(k1_wellord1(A_444, B_446), B_447))), inference(resolution, [status(thm)], [c_4171, c_12])).
% 32.66/21.91  tff(c_4721, plain, (![B_448, A_449, B_450]: (r2_hidden(B_448, k3_relat_1(A_449)) | r1_tarski(k1_wellord1(A_449, k3_relat_1(A_449)), B_450) | ~v1_relat_1(A_449))), inference(resolution, [status(thm)], [c_2976, c_4713])).
% 32.66/21.91  tff(c_5072, plain, (![A_455, B_456, B_457]: (~r1_tarski(k3_relat_1(A_455), B_456) | r1_tarski(k1_wellord1(A_455, k3_relat_1(A_455)), B_457) | ~v1_relat_1(A_455))), inference(resolution, [status(thm)], [c_4721, c_12])).
% 32.66/21.91  tff(c_5079, plain, (![A_458, B_459]: (r1_tarski(k1_wellord1(A_458, k3_relat_1(A_458)), B_459) | ~v1_relat_1(A_458))), inference(resolution, [status(thm)], [c_140, c_5072])).
% 32.66/21.91  tff(c_490, plain, (![A_150, B_151]: (r2_hidden('#skF_7'(A_150, B_151), B_151) | k1_xboole_0=B_151 | ~r1_tarski(B_151, k3_relat_1(A_150)) | ~v2_wellord1(A_150) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_122])).
% 32.66/21.91  tff(c_520, plain, (![B_151, A_150]: (~r1_tarski(B_151, '#skF_7'(A_150, B_151)) | k1_xboole_0=B_151 | ~r1_tarski(B_151, k3_relat_1(A_150)) | ~v2_wellord1(A_150) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_490, c_12])).
% 32.66/21.91  tff(c_27079, plain, (![A_1180, A_1181]: (k1_wellord1(A_1180, k3_relat_1(A_1180))=k1_xboole_0 | ~r1_tarski(k1_wellord1(A_1180, k3_relat_1(A_1180)), k3_relat_1(A_1181)) | ~v2_wellord1(A_1181) | ~v1_relat_1(A_1181) | ~v1_relat_1(A_1180))), inference(resolution, [status(thm)], [c_5079, c_520])).
% 32.66/21.91  tff(c_27160, plain, (![B_1182]: (k1_wellord1(B_1182, k3_relat_1(B_1182))=k1_xboole_0 | ~v2_wellord1(B_1182) | ~v1_relat_1(B_1182))), inference(resolution, [status(thm)], [c_66, c_27079])).
% 32.66/21.91  tff(c_305, plain, (![B_129, A_130, B_131]: (r2_hidden(B_129, k3_relat_1(A_130)) | ~v1_relat_1(A_130) | r1_tarski(k1_wellord1(A_130, B_129), B_131))), inference(resolution, [status(thm)], [c_6, c_270])).
% 32.66/21.91  tff(c_350, plain, (![A_130, B_129, B_131]: (~r1_tarski(k3_relat_1(A_130), B_129) | ~v1_relat_1(A_130) | r1_tarski(k1_wellord1(A_130, B_129), B_131))), inference(resolution, [status(thm)], [c_305, c_12])).
% 32.66/21.91  tff(c_27347, plain, (![B_1182, B_131]: (~r1_tarski(k3_relat_1(B_1182), k3_relat_1(B_1182)) | ~v1_relat_1(B_1182) | r1_tarski(k1_xboole_0, B_131) | ~v2_wellord1(B_1182) | ~v1_relat_1(B_1182))), inference(superposition, [status(thm), theory('equality')], [c_27160, c_350])).
% 32.66/21.91  tff(c_27422, plain, (![B_131, B_1182]: (r1_tarski(k1_xboole_0, B_131) | ~v2_wellord1(B_1182) | ~v1_relat_1(B_1182))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_27347])).
% 32.66/21.91  tff(c_27425, plain, (![B_1183]: (~v2_wellord1(B_1183) | ~v1_relat_1(B_1183))), inference(splitLeft, [status(thm)], [c_27422])).
% 32.66/21.91  tff(c_27428, plain, (~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_88, c_27425])).
% 32.66/21.91  tff(c_27432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_27428])).
% 32.66/21.91  tff(c_27433, plain, (![B_131]: (r1_tarski(k1_xboole_0, B_131))), inference(splitRight, [status(thm)], [c_27422])).
% 32.66/21.91  tff(c_36, plain, (![A_23]: (v6_relat_2(A_23) | ~v2_wellord1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.66/21.91  tff(c_84, plain, (r2_hidden('#skF_12', k3_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 32.66/21.91  tff(c_86, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 32.66/21.91  tff(c_2502, plain, (![C_289, B_290, A_291]: (r2_hidden(k4_tarski(C_289, B_290), A_291) | r2_hidden(k4_tarski(B_290, C_289), A_291) | C_289=B_290 | ~r2_hidden(C_289, k3_relat_1(A_291)) | ~r2_hidden(B_290, k3_relat_1(A_291)) | ~v6_relat_2(A_291) | ~v1_relat_1(A_291))), inference(cnfTransformation, [status(thm)], [f_91])).
% 32.66/21.91  tff(c_92, plain, (~r1_tarski(k1_wellord1('#skF_13', '#skF_11'), k1_wellord1('#skF_13', '#skF_12')) | ~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_163])).
% 32.66/21.91  tff(c_130, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_92])).
% 32.66/21.91  tff(c_2546, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_13') | '#skF_11'='#skF_12' | ~r2_hidden('#skF_11', k3_relat_1('#skF_13')) | ~r2_hidden('#skF_12', k3_relat_1('#skF_13')) | ~v6_relat_2('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_2502, c_130])).
% 32.66/21.91  tff(c_2619, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_13') | '#skF_11'='#skF_12' | ~v6_relat_2('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_84, c_86, c_2546])).
% 32.66/21.91  tff(c_2639, plain, (~v6_relat_2('#skF_13')), inference(splitLeft, [status(thm)], [c_2619])).
% 32.66/21.91  tff(c_2645, plain, (~v2_wellord1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_36, c_2639])).
% 32.66/21.91  tff(c_2652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_2645])).
% 32.66/21.91  tff(c_2654, plain, (v6_relat_2('#skF_13')), inference(splitRight, [status(thm)], [c_2619])).
% 32.66/21.91  tff(c_2597, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_13') | '#skF_11'='#skF_12' | ~r2_hidden('#skF_12', k3_relat_1('#skF_13')) | ~r2_hidden('#skF_11', k3_relat_1('#skF_13')) | ~v6_relat_2('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_2502, c_130])).
% 32.66/21.91  tff(c_2636, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_13') | '#skF_11'='#skF_12' | ~v6_relat_2('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_2597])).
% 32.66/21.91  tff(c_2656, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_13') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_2636])).
% 32.66/21.91  tff(c_2657, plain, ('#skF_11'='#skF_12'), inference(splitLeft, [status(thm)], [c_2656])).
% 32.66/21.91  tff(c_601, plain, (r2_hidden('#skF_11', '#skF_6'('#skF_13', '#skF_12')) | ~r2_hidden('#skF_11', k3_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_558, c_130])).
% 32.66/21.91  tff(c_623, plain, (r2_hidden('#skF_11', '#skF_6'('#skF_13', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_601])).
% 32.66/21.91  tff(c_2689, plain, (r2_hidden('#skF_12', '#skF_6'('#skF_13', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_623])).
% 32.66/21.91  tff(c_64, plain, (![A_38, B_46]: (r2_hidden('#skF_7'(A_38, B_46), B_46) | k1_xboole_0=B_46 | ~r1_tarski(B_46, k3_relat_1(A_38)) | ~v2_wellord1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 32.66/21.91  tff(c_1305, plain, (![A_220, B_221, D_222]: (r2_hidden(k4_tarski('#skF_7'(A_220, B_221), D_222), A_220) | ~r2_hidden(D_222, B_221) | k1_xboole_0=B_221 | ~r1_tarski(B_221, k3_relat_1(A_220)) | ~v2_wellord1(A_220) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_122])).
% 32.66/21.91  tff(c_58, plain, (![D_37, B_32, A_31]: (~r2_hidden(k4_tarski(D_37, B_32), A_31) | ~r2_hidden(D_37, '#skF_6'(A_31, B_32)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_102])).
% 32.66/21.91  tff(c_10067, plain, (![A_680, B_681, D_682]: (~r2_hidden('#skF_7'(A_680, B_681), '#skF_6'(A_680, D_682)) | ~r2_hidden(D_682, B_681) | k1_xboole_0=B_681 | ~r1_tarski(B_681, k3_relat_1(A_680)) | ~v2_wellord1(A_680) | ~v1_relat_1(A_680))), inference(resolution, [status(thm)], [c_1305, c_58])).
% 32.66/21.91  tff(c_72382, plain, (![D_1769, A_1770]: (~r2_hidden(D_1769, '#skF_6'(A_1770, D_1769)) | '#skF_6'(A_1770, D_1769)=k1_xboole_0 | ~r1_tarski('#skF_6'(A_1770, D_1769), k3_relat_1(A_1770)) | ~v2_wellord1(A_1770) | ~v1_relat_1(A_1770))), inference(resolution, [status(thm)], [c_64, c_10067])).
% 32.66/21.91  tff(c_72636, plain, ('#skF_6'('#skF_13', '#skF_12')=k1_xboole_0 | ~r1_tarski('#skF_6'('#skF_13', '#skF_12'), k3_relat_1('#skF_13')) | ~v2_wellord1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_2689, c_72382])).
% 32.66/21.91  tff(c_72863, plain, ('#skF_6'('#skF_13', '#skF_12')=k1_xboole_0 | ~r1_tarski('#skF_6'('#skF_13', '#skF_12'), k3_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_72636])).
% 32.66/21.91  tff(c_72894, plain, (~r1_tarski('#skF_6'('#skF_13', '#skF_12'), k3_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_72863])).
% 32.66/21.91  tff(c_72898, plain, (~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_2976, c_72894])).
% 32.66/21.91  tff(c_72902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_72898])).
% 32.66/21.91  tff(c_72903, plain, ('#skF_6'('#skF_13', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_72863])).
% 32.66/21.91  tff(c_144, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.66/21.91  tff(c_195, plain, (![A_108, B_109, B_110]: (r2_hidden('#skF_1'(A_108, B_109), B_110) | ~r1_tarski(A_108, B_110) | r1_tarski(A_108, B_109))), inference(resolution, [status(thm)], [c_6, c_144])).
% 32.66/21.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.66/21.91  tff(c_678, plain, (![A_170, B_171, B_172, B_173]: (r2_hidden('#skF_1'(A_170, B_171), B_172) | ~r1_tarski(B_173, B_172) | ~r1_tarski(A_170, B_173) | r1_tarski(A_170, B_171))), inference(resolution, [status(thm)], [c_195, c_2])).
% 32.66/21.91  tff(c_712, plain, (![A_178, B_179]: (r2_hidden('#skF_1'(A_178, B_179), k1_wellord1('#skF_13', '#skF_12')) | ~r1_tarski(A_178, k1_wellord1('#skF_13', '#skF_11')) | r1_tarski(A_178, B_179))), inference(resolution, [status(thm)], [c_115, c_678])).
% 32.66/21.91  tff(c_257, plain, (![D_117, A_119, B_118]: (~r2_hidden(D_117, '#skF_6'(A_119, B_118)) | ~r2_hidden(D_117, k1_wellord1(A_119, B_118)) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_224, c_58])).
% 32.66/21.91  tff(c_715, plain, (![A_178, B_179]: (~r2_hidden('#skF_1'(A_178, B_179), '#skF_6'('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13') | ~r1_tarski(A_178, k1_wellord1('#skF_13', '#skF_11')) | r1_tarski(A_178, B_179))), inference(resolution, [status(thm)], [c_712, c_257])).
% 32.66/21.91  tff(c_735, plain, (![A_178, B_179]: (~r2_hidden('#skF_1'(A_178, B_179), '#skF_6'('#skF_13', '#skF_12')) | ~r1_tarski(A_178, k1_wellord1('#skF_13', '#skF_11')) | r1_tarski(A_178, B_179))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_715])).
% 32.66/21.91  tff(c_3290, plain, (![A_348, B_349]: (~r2_hidden('#skF_1'(A_348, B_349), '#skF_6'('#skF_13', '#skF_12')) | ~r1_tarski(A_348, k1_wellord1('#skF_13', '#skF_12')) | r1_tarski(A_348, B_349))), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_735])).
% 32.66/21.91  tff(c_3318, plain, (![B_2]: (~r1_tarski('#skF_6'('#skF_13', '#skF_12'), k1_wellord1('#skF_13', '#skF_12')) | r1_tarski('#skF_6'('#skF_13', '#skF_12'), B_2))), inference(resolution, [status(thm)], [c_6, c_3290])).
% 32.66/21.91  tff(c_3383, plain, (~r1_tarski('#skF_6'('#skF_13', '#skF_12'), k1_wellord1('#skF_13', '#skF_12'))), inference(splitLeft, [status(thm)], [c_3318])).
% 32.66/21.91  tff(c_72908, plain, (~r1_tarski(k1_xboole_0, k1_wellord1('#skF_13', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_72903, c_3383])).
% 32.66/21.91  tff(c_72915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27433, c_72908])).
% 32.66/21.91  tff(c_72916, plain, (![B_2]: (r1_tarski('#skF_6'('#skF_13', '#skF_12'), B_2))), inference(splitRight, [status(thm)], [c_3318])).
% 32.66/21.91  tff(c_637, plain, (~r1_tarski('#skF_6'('#skF_13', '#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_623, c_12])).
% 32.66/21.91  tff(c_2688, plain, (~r1_tarski('#skF_6'('#skF_13', '#skF_12'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_637])).
% 32.66/21.91  tff(c_72923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72916, c_2688])).
% 32.66/21.91  tff(c_72925, plain, ('#skF_11'!='#skF_12'), inference(splitRight, [status(thm)], [c_2656])).
% 32.66/21.91  tff(c_72924, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_13')), inference(splitRight, [status(thm)], [c_2656])).
% 32.66/21.91  tff(c_14, plain, (![D_22, A_11, B_18]: (r2_hidden(D_22, k1_wellord1(A_11, B_18)) | ~r2_hidden(k4_tarski(D_22, B_18), A_11) | D_22=B_18 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.66/21.91  tff(c_72928, plain, (r2_hidden('#skF_12', k1_wellord1('#skF_13', '#skF_11')) | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_72924, c_14])).
% 32.66/21.91  tff(c_72945, plain, (r2_hidden('#skF_12', k1_wellord1('#skF_13', '#skF_11')) | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_72928])).
% 32.66/21.91  tff(c_72946, plain, (r2_hidden('#skF_12', k1_wellord1('#skF_13', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_72925, c_72945])).
% 32.66/21.91  tff(c_73185, plain, (![B_1775]: (r2_hidden('#skF_12', B_1775) | ~r1_tarski(k1_wellord1('#skF_13', '#skF_11'), B_1775))), inference(resolution, [status(thm)], [c_72946, c_2])).
% 32.66/21.91  tff(c_73221, plain, (r2_hidden('#skF_12', k1_wellord1('#skF_13', '#skF_12'))), inference(resolution, [status(thm)], [c_115, c_73185])).
% 32.66/21.91  tff(c_18, plain, (![D_22, A_11]: (~r2_hidden(D_22, k1_wellord1(A_11, D_22)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.66/21.91  tff(c_73237, plain, (~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_73221, c_18])).
% 32.66/21.91  tff(c_73257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_73237])).
% 32.66/21.91  tff(c_73258, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_13')), inference(splitRight, [status(thm)], [c_98])).
% 32.66/21.91  tff(c_73273, plain, (~r1_tarski(k1_wellord1('#skF_13', '#skF_11'), k1_wellord1('#skF_13', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_73258, c_92])).
% 32.66/21.91  tff(c_73283, plain, (![A_1785, B_1786]: (~r2_hidden('#skF_1'(A_1785, B_1786), B_1786) | r1_tarski(A_1785, B_1786))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.66/21.91  tff(c_73288, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_73283])).
% 32.66/21.91  tff(c_73799, plain, (![D_1870, A_1871, B_1872]: (r2_hidden(D_1870, k1_wellord1(A_1871, B_1872)) | ~r2_hidden(k4_tarski(D_1870, B_1872), A_1871) | D_1870=B_1872 | ~v1_relat_1(A_1871))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.66/21.91  tff(c_73816, plain, (r2_hidden('#skF_11', k1_wellord1('#skF_13', '#skF_12')) | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_73258, c_73799])).
% 32.66/21.91  tff(c_73823, plain, (r2_hidden('#skF_11', k1_wellord1('#skF_13', '#skF_12')) | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_73816])).
% 32.66/21.91  tff(c_73824, plain, ('#skF_11'='#skF_12'), inference(splitLeft, [status(thm)], [c_73823])).
% 32.66/21.91  tff(c_73836, plain, (~r1_tarski(k1_wellord1('#skF_13', '#skF_12'), k1_wellord1('#skF_13', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_73824, c_73273])).
% 32.66/21.91  tff(c_73843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73288, c_73836])).
% 32.66/21.91  tff(c_73844, plain, (r2_hidden('#skF_11', k1_wellord1('#skF_13', '#skF_12'))), inference(splitRight, [status(thm)], [c_73823])).
% 32.66/21.91  tff(c_16, plain, (![D_22, B_18, A_11]: (r2_hidden(k4_tarski(D_22, B_18), A_11) | ~r2_hidden(D_22, k1_wellord1(A_11, B_18)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.66/21.91  tff(c_77677, plain, (![C_2121, B_2122, D_2123, C_2124]: (~r2_hidden(C_2121, k3_relat_1(B_2122)) | r2_hidden(D_2123, k1_wellord1(B_2122, C_2121)) | ~r2_hidden(k4_tarski(D_2123, C_2124), B_2122) | ~r2_hidden(C_2124, k1_wellord1(B_2122, C_2121)) | ~r1_tarski(k1_wellord1(B_2122, C_2121), k3_relat_1(B_2122)) | ~v2_wellord1(B_2122) | ~v1_relat_1(B_2122))), inference(cnfTransformation, [status(thm)], [f_150])).
% 32.66/21.91  tff(c_115268, plain, (![C_3412, A_3413, D_3414, B_3415]: (~r2_hidden(C_3412, k3_relat_1(A_3413)) | r2_hidden(D_3414, k1_wellord1(A_3413, C_3412)) | ~r2_hidden(B_3415, k1_wellord1(A_3413, C_3412)) | ~r1_tarski(k1_wellord1(A_3413, C_3412), k3_relat_1(A_3413)) | ~v2_wellord1(A_3413) | ~r2_hidden(D_3414, k1_wellord1(A_3413, B_3415)) | ~v1_relat_1(A_3413))), inference(resolution, [status(thm)], [c_16, c_77677])).
% 32.66/21.91  tff(c_115406, plain, (![D_3414]: (~r2_hidden('#skF_12', k3_relat_1('#skF_13')) | r2_hidden(D_3414, k1_wellord1('#skF_13', '#skF_12')) | ~r1_tarski(k1_wellord1('#skF_13', '#skF_12'), k3_relat_1('#skF_13')) | ~v2_wellord1('#skF_13') | ~r2_hidden(D_3414, k1_wellord1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_73844, c_115268])).
% 32.66/21.91  tff(c_115467, plain, (![D_3414]: (r2_hidden(D_3414, k1_wellord1('#skF_13', '#skF_12')) | ~r1_tarski(k1_wellord1('#skF_13', '#skF_12'), k3_relat_1('#skF_13')) | ~r2_hidden(D_3414, k1_wellord1('#skF_13', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_115406])).
% 32.66/21.91  tff(c_115475, plain, (~r1_tarski(k1_wellord1('#skF_13', '#skF_12'), k3_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_115467])).
% 32.66/21.91  tff(c_115495, plain, (~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_66, c_115475])).
% 32.66/21.91  tff(c_115514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_115495])).
% 32.66/21.91  tff(c_115672, plain, (![D_3419]: (r2_hidden(D_3419, k1_wellord1('#skF_13', '#skF_12')) | ~r2_hidden(D_3419, k1_wellord1('#skF_13', '#skF_11')))), inference(splitRight, [status(thm)], [c_115467])).
% 32.66/21.91  tff(c_116102, plain, (![B_3426]: (r2_hidden('#skF_1'(k1_wellord1('#skF_13', '#skF_11'), B_3426), k1_wellord1('#skF_13', '#skF_12')) | r1_tarski(k1_wellord1('#skF_13', '#skF_11'), B_3426))), inference(resolution, [status(thm)], [c_6, c_115672])).
% 32.66/21.91  tff(c_116121, plain, (r1_tarski(k1_wellord1('#skF_13', '#skF_11'), k1_wellord1('#skF_13', '#skF_12'))), inference(resolution, [status(thm)], [c_116102, c_4])).
% 32.66/21.91  tff(c_116148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73273, c_73273, c_116121])).
% 32.66/21.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.66/21.91  
% 32.66/21.91  Inference rules
% 32.66/21.91  ----------------------
% 32.66/21.91  #Ref     : 0
% 32.66/21.91  #Sup     : 25920
% 32.66/21.91  #Fact    : 50
% 32.66/21.91  #Define  : 0
% 32.66/21.91  #Split   : 89
% 32.66/21.91  #Chain   : 0
% 32.66/21.91  #Close   : 0
% 32.66/21.91  
% 32.66/21.91  Ordering : KBO
% 32.66/21.91  
% 32.66/21.91  Simplification rules
% 32.66/21.91  ----------------------
% 32.66/21.91  #Subsume      : 11751
% 32.66/21.91  #Demod        : 8099
% 32.66/21.91  #Tautology    : 1609
% 32.66/21.91  #SimpNegUnit  : 452
% 32.66/21.91  #BackRed      : 261
% 32.66/21.91  
% 32.66/21.91  #Partial instantiations: 0
% 32.66/21.91  #Strategies tried      : 1
% 32.66/21.91  
% 32.66/21.91  Timing (in seconds)
% 32.66/21.91  ----------------------
% 32.66/21.91  Preprocessing        : 0.39
% 32.66/21.91  Parsing              : 0.19
% 32.66/21.91  CNF conversion       : 0.04
% 32.66/21.91  Main loop            : 20.71
% 32.66/21.91  Inferencing          : 3.91
% 32.66/21.91  Reduction            : 4.71
% 32.66/21.91  Demodulation         : 3.07
% 32.66/21.91  BG Simplification    : 0.36
% 32.66/21.91  Subsumption          : 10.43
% 32.66/21.91  Abstraction          : 0.63
% 32.66/21.91  MUC search           : 0.00
% 32.66/21.91  Cooper               : 0.00
% 32.66/21.91  Total                : 21.15
% 32.66/21.91  Index Insertion      : 0.00
% 32.66/21.91  Index Deletion       : 0.00
% 32.66/21.91  Index Matching       : 0.00
% 32.66/21.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
