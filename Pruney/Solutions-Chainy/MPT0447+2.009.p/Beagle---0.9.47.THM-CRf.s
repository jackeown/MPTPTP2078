%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:29 EST 2020

% Result     : Theorem 17.45s
% Output     : CNFRefutation 17.45s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 229 expanded)
%              Number of leaves         :   54 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 445 expanded)
%              Number of equality atoms :   38 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_11 > #skF_6 > #skF_2 > #skF_13 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_196,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_81,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_151,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_179,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_145,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ~ ( r2_hidden(C,B)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & ! [E] :
                      ( r1_tarski(E,C)
                     => r2_hidden(E,D) ) ) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).

tff(f_112,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_87,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
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

tff(f_147,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_186,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_163,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_170,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_86,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_30,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_112,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(A_124,B_125) = k1_xboole_0
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_126,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_88,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_95,plain,(
    ! [A_117] :
      ( v1_relat_1(A_117)
      | ~ v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_78,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_11'(A_107,B_108),k1_relat_1(B_108))
      | ~ r2_hidden(A_107,k2_relat_1(B_108))
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1621,plain,(
    ! [C_244,A_245] :
      ( r2_hidden(k4_tarski(C_244,'#skF_10'(A_245,k1_relat_1(A_245),C_244)),A_245)
      | ~ r2_hidden(C_244,k1_relat_1(A_245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    ! [A_40] : r2_hidden(A_40,'#skF_5'(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_289,plain,(
    ! [C_151,A_152,D_153] :
      ( r2_hidden(C_151,k1_relat_1(A_152))
      | ~ r2_hidden(k4_tarski(C_151,D_153),A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_294,plain,(
    ! [C_151,D_153] : r2_hidden(C_151,k1_relat_1('#skF_5'(k4_tarski(C_151,D_153)))) ),
    inference(resolution,[status(thm)],[c_52,c_289])).

tff(c_46,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_4'(A_33,B_34),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_310,plain,(
    ! [A_157,B_158,C_159] :
      ( ~ r1_xboole_0(A_157,B_158)
      | ~ r2_hidden(C_159,B_158)
      | ~ r2_hidden(C_159,A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_314,plain,(
    ! [C_160,A_161] :
      ( ~ r2_hidden(C_160,k1_xboole_0)
      | ~ r2_hidden(C_160,A_161) ) ),
    inference(resolution,[status(thm)],[c_34,c_310])).

tff(c_361,plain,(
    ! [A_167,A_168] :
      ( ~ r2_hidden('#skF_4'(A_167,k1_xboole_0),A_168)
      | ~ r2_hidden(A_167,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_46,c_314])).

tff(c_372,plain,(
    ! [A_167] : ~ r2_hidden(A_167,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_294,c_361])).

tff(c_1640,plain,(
    ! [C_246] : ~ r2_hidden(C_246,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1621,c_372])).

tff(c_1648,plain,(
    ! [A_107] :
      ( ~ r2_hidden(A_107,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_78,c_1640])).

tff(c_1709,plain,(
    ! [A_247] : ~ r2_hidden(A_247,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_1648])).

tff(c_1734,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1709])).

tff(c_84,plain,(
    r1_tarski('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_127,plain,(
    k4_xboole_0('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_112])).

tff(c_58,plain,(
    ! [A_81,B_82] : k6_subset_1(A_81,B_82) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_80,plain,(
    ! [A_110,B_112] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_110),k2_relat_1(B_112)),k2_relat_1(k6_subset_1(A_110,B_112)))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1890,plain,(
    ! [A_255,B_256] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_255),k2_relat_1(B_256)),k2_relat_1(k4_xboole_0(A_255,B_256)))
      | ~ v1_relat_1(B_256)
      | ~ v1_relat_1(A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_80])).

tff(c_1937,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1890])).

tff(c_1961,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1734,c_1937])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_202,plain,(
    ! [B_139,A_140] :
      ( B_139 = A_140
      | ~ r1_tarski(B_139,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_216,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_202])).

tff(c_1975,plain,
    ( k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1961,c_216])).

tff(c_1992,plain,(
    k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1975])).

tff(c_16,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3342,plain,(
    ! [C_286,A_287,B_288] :
      ( r1_tarski(C_286,'#skF_3'(A_287,B_288,C_286))
      | k2_xboole_0(A_287,C_286) = B_288
      | ~ r1_tarski(C_286,B_288)
      | ~ r1_tarski(A_287,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [B_16,A_15,C_17] :
      ( ~ r1_tarski(B_16,'#skF_3'(A_15,B_16,C_17))
      | k2_xboole_0(A_15,C_17) = B_16
      | ~ r1_tarski(C_17,B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3349,plain,(
    ! [A_287,B_288] :
      ( k2_xboole_0(A_287,B_288) = B_288
      | ~ r1_tarski(B_288,B_288)
      | ~ r1_tarski(A_287,B_288) ) ),
    inference(resolution,[status(thm)],[c_3342,c_24])).

tff(c_3376,plain,(
    ! [A_289,B_290] :
      ( k2_xboole_0(A_289,B_290) = B_290
      | ~ r1_tarski(A_289,B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3349])).

tff(c_3871,plain,(
    ! [A_295,B_296] :
      ( k2_xboole_0(A_295,B_296) = B_296
      | k4_xboole_0(A_295,B_296) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_3376])).

tff(c_3923,plain,(
    k2_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) = k2_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_1992,c_3871])).

tff(c_36,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4166,plain,(
    r1_tarski(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3923,c_36])).

tff(c_263,plain,(
    ! [A_149] :
      ( k2_xboole_0(k1_relat_1(A_149),k2_relat_1(A_149)) = k3_relat_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_22,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_269,plain,(
    ! [A_12,A_149] :
      ( r1_tarski(A_12,k3_relat_1(A_149))
      | ~ r1_tarski(A_12,k2_relat_1(A_149))
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_22])).

tff(c_1672,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1640])).

tff(c_76,plain,(
    ! [A_104,B_106] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_104),k1_relat_1(B_106)),k1_relat_1(k6_subset_1(A_104,B_106)))
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2207,plain,(
    ! [A_260,B_261] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_260),k1_relat_1(B_261)),k1_relat_1(k4_xboole_0(A_260,B_261)))
      | ~ v1_relat_1(B_261)
      | ~ v1_relat_1(A_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_76])).

tff(c_2260,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_2207])).

tff(c_2287,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1672,c_2260])).

tff(c_2301,plain,
    ( k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2287,c_216])).

tff(c_2318,plain,(
    k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_2301])).

tff(c_3921,plain,(
    k2_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) = k1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_2318,c_3871])).

tff(c_4078,plain,(
    r1_tarski(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3921,c_36])).

tff(c_275,plain,(
    ! [A_149] :
      ( r1_tarski(k1_relat_1(A_149),k3_relat_1(A_149))
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_36])).

tff(c_719,plain,(
    ! [A_195,C_196,B_197] :
      ( r1_tarski(k2_xboole_0(A_195,C_196),B_197)
      | ~ r1_tarski(C_196,B_197)
      | ~ r1_tarski(A_195,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_217,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(k2_xboole_0(A_24,B_25),A_24) ) ),
    inference(resolution,[status(thm)],[c_36,c_202])).

tff(c_735,plain,(
    ! [B_197,C_196] :
      ( k2_xboole_0(B_197,C_196) = B_197
      | ~ r1_tarski(C_196,B_197)
      | ~ r1_tarski(B_197,B_197) ) ),
    inference(resolution,[status(thm)],[c_719,c_217])).

tff(c_763,plain,(
    ! [B_198,C_199] :
      ( k2_xboole_0(B_198,C_199) = B_198
      | ~ r1_tarski(C_199,B_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_735])).

tff(c_1463,plain,(
    ! [A_239] :
      ( k2_xboole_0(k3_relat_1(A_239),k1_relat_1(A_239)) = k3_relat_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(resolution,[status(thm)],[c_275,c_763])).

tff(c_49624,plain,(
    ! [A_825,A_826] :
      ( r1_tarski(A_825,k3_relat_1(A_826))
      | ~ r1_tarski(A_825,k1_relat_1(A_826))
      | ~ v1_relat_1(A_826) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_22])).

tff(c_74,plain,(
    ! [A_103] :
      ( k2_xboole_0(k1_relat_1(A_103),k2_relat_1(A_103)) = k3_relat_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_12043,plain,(
    ! [A_411,B_412] :
      ( r1_tarski(k3_relat_1(A_411),B_412)
      | ~ r1_tarski(k2_relat_1(A_411),B_412)
      | ~ r1_tarski(k1_relat_1(A_411),B_412)
      | ~ v1_relat_1(A_411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_719])).

tff(c_82,plain,(
    ~ r1_tarski(k3_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_12145,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_12043,c_82])).

tff(c_12184,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_12145])).

tff(c_12207,plain,(
    ~ r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_12184])).

tff(c_49658,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_12'),k1_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_49624,c_12207])).

tff(c_49710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4078,c_49658])).

tff(c_49711,plain,(
    ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(splitRight,[status(thm)],[c_12184])).

tff(c_49715,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k2_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_269,c_49711])).

tff(c_49725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4166,c_49715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:39:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.45/8.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.45/8.94  
% 17.45/8.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.45/8.94  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_11 > #skF_6 > #skF_2 > #skF_13 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_4 > #skF_10
% 17.45/8.94  
% 17.45/8.94  %Foreground sorts:
% 17.45/8.94  
% 17.45/8.94  
% 17.45/8.94  %Background operators:
% 17.45/8.94  
% 17.45/8.94  
% 17.45/8.94  %Foreground operators:
% 17.45/8.94  tff('#skF_5', type, '#skF_5': $i > $i).
% 17.45/8.94  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 17.45/8.94  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 17.45/8.94  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 17.45/8.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 17.45/8.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.45/8.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.45/8.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.45/8.94  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.45/8.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.45/8.94  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 17.45/8.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.45/8.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.45/8.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.45/8.94  tff('#skF_13', type, '#skF_13': $i).
% 17.45/8.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.45/8.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.45/8.94  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 17.45/8.94  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 17.45/8.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.45/8.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.45/8.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.45/8.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.45/8.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.45/8.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.45/8.94  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 17.45/8.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.45/8.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.45/8.94  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 17.45/8.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.45/8.94  tff('#skF_12', type, '#skF_12': $i).
% 17.45/8.94  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 17.45/8.94  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 17.45/8.94  
% 17.45/8.96  tff(f_196, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 17.45/8.96  tff(f_81, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.45/8.96  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 17.45/8.96  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 17.45/8.96  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 17.45/8.96  tff(f_151, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 17.45/8.96  tff(f_179, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 17.45/8.96  tff(f_159, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 17.45/8.96  tff(f_145, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & (![E]: (r1_tarski(E, C) => r2_hidden(E, D)))))))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tarski)).
% 17.45/8.96  tff(f_112, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 17.45/8.96  tff(f_87, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 17.45/8.96  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 17.45/8.96  tff(f_147, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 17.45/8.96  tff(f_186, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 17.45/8.96  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.45/8.96  tff(f_79, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 17.45/8.96  tff(f_89, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 17.45/8.96  tff(f_163, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 17.45/8.96  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 17.45/8.96  tff(f_170, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 17.45/8.96  tff(f_95, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 17.45/8.96  tff(c_86, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_196])).
% 17.45/8.96  tff(c_30, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.45/8.96  tff(c_112, plain, (![A_124, B_125]: (k4_xboole_0(A_124, B_125)=k1_xboole_0 | ~r1_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.45/8.96  tff(c_126, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_112])).
% 17.45/8.96  tff(c_88, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_196])).
% 17.45/8.96  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.45/8.96  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 17.45/8.96  tff(c_95, plain, (![A_117]: (v1_relat_1(A_117) | ~v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_151])).
% 17.45/8.96  tff(c_99, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_95])).
% 17.45/8.96  tff(c_78, plain, (![A_107, B_108]: (r2_hidden('#skF_11'(A_107, B_108), k1_relat_1(B_108)) | ~r2_hidden(A_107, k2_relat_1(B_108)) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_179])).
% 17.45/8.96  tff(c_1621, plain, (![C_244, A_245]: (r2_hidden(k4_tarski(C_244, '#skF_10'(A_245, k1_relat_1(A_245), C_244)), A_245) | ~r2_hidden(C_244, k1_relat_1(A_245)))), inference(cnfTransformation, [status(thm)], [f_159])).
% 17.45/8.96  tff(c_52, plain, (![A_40]: (r2_hidden(A_40, '#skF_5'(A_40)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 17.45/8.96  tff(c_289, plain, (![C_151, A_152, D_153]: (r2_hidden(C_151, k1_relat_1(A_152)) | ~r2_hidden(k4_tarski(C_151, D_153), A_152))), inference(cnfTransformation, [status(thm)], [f_159])).
% 17.45/8.96  tff(c_294, plain, (![C_151, D_153]: (r2_hidden(C_151, k1_relat_1('#skF_5'(k4_tarski(C_151, D_153)))))), inference(resolution, [status(thm)], [c_52, c_289])).
% 17.45/8.96  tff(c_46, plain, (![A_33, B_34]: (r2_hidden('#skF_4'(A_33, B_34), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_112])).
% 17.45/8.96  tff(c_34, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.45/8.96  tff(c_310, plain, (![A_157, B_158, C_159]: (~r1_xboole_0(A_157, B_158) | ~r2_hidden(C_159, B_158) | ~r2_hidden(C_159, A_157))), inference(cnfTransformation, [status(thm)], [f_44])).
% 17.45/8.96  tff(c_314, plain, (![C_160, A_161]: (~r2_hidden(C_160, k1_xboole_0) | ~r2_hidden(C_160, A_161))), inference(resolution, [status(thm)], [c_34, c_310])).
% 17.45/8.96  tff(c_361, plain, (![A_167, A_168]: (~r2_hidden('#skF_4'(A_167, k1_xboole_0), A_168) | ~r2_hidden(A_167, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_314])).
% 17.45/8.96  tff(c_372, plain, (![A_167]: (~r2_hidden(A_167, k1_xboole_0))), inference(resolution, [status(thm)], [c_294, c_361])).
% 17.45/8.96  tff(c_1640, plain, (![C_246]: (~r2_hidden(C_246, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1621, c_372])).
% 17.45/8.96  tff(c_1648, plain, (![A_107]: (~r2_hidden(A_107, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_78, c_1640])).
% 17.45/8.96  tff(c_1709, plain, (![A_247]: (~r2_hidden(A_247, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_1648])).
% 17.45/8.96  tff(c_1734, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1709])).
% 17.45/8.96  tff(c_84, plain, (r1_tarski('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_196])).
% 17.45/8.96  tff(c_127, plain, (k4_xboole_0('#skF_12', '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_112])).
% 17.45/8.96  tff(c_58, plain, (![A_81, B_82]: (k6_subset_1(A_81, B_82)=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.45/8.96  tff(c_80, plain, (![A_110, B_112]: (r1_tarski(k6_subset_1(k2_relat_1(A_110), k2_relat_1(B_112)), k2_relat_1(k6_subset_1(A_110, B_112))) | ~v1_relat_1(B_112) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_186])).
% 17.45/8.96  tff(c_1890, plain, (![A_255, B_256]: (r1_tarski(k4_xboole_0(k2_relat_1(A_255), k2_relat_1(B_256)), k2_relat_1(k4_xboole_0(A_255, B_256))) | ~v1_relat_1(B_256) | ~v1_relat_1(A_255))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_80])).
% 17.45/8.96  tff(c_1937, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_127, c_1890])).
% 17.45/8.96  tff(c_1961, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_1734, c_1937])).
% 17.45/8.96  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.45/8.96  tff(c_202, plain, (![B_139, A_140]: (B_139=A_140 | ~r1_tarski(B_139, A_140) | ~r1_tarski(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.45/8.96  tff(c_216, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_202])).
% 17.45/8.96  tff(c_1975, plain, (k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1961, c_216])).
% 17.45/8.96  tff(c_1992, plain, (k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_126, c_1975])).
% 17.45/8.96  tff(c_16, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.45/8.96  tff(c_3342, plain, (![C_286, A_287, B_288]: (r1_tarski(C_286, '#skF_3'(A_287, B_288, C_286)) | k2_xboole_0(A_287, C_286)=B_288 | ~r1_tarski(C_286, B_288) | ~r1_tarski(A_287, B_288))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.45/8.96  tff(c_24, plain, (![B_16, A_15, C_17]: (~r1_tarski(B_16, '#skF_3'(A_15, B_16, C_17)) | k2_xboole_0(A_15, C_17)=B_16 | ~r1_tarski(C_17, B_16) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.45/8.96  tff(c_3349, plain, (![A_287, B_288]: (k2_xboole_0(A_287, B_288)=B_288 | ~r1_tarski(B_288, B_288) | ~r1_tarski(A_287, B_288))), inference(resolution, [status(thm)], [c_3342, c_24])).
% 17.45/8.96  tff(c_3376, plain, (![A_289, B_290]: (k2_xboole_0(A_289, B_290)=B_290 | ~r1_tarski(A_289, B_290))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3349])).
% 17.45/8.96  tff(c_3871, plain, (![A_295, B_296]: (k2_xboole_0(A_295, B_296)=B_296 | k4_xboole_0(A_295, B_296)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_3376])).
% 17.45/8.96  tff(c_3923, plain, (k2_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))=k2_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1992, c_3871])).
% 17.45/8.96  tff(c_36, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.45/8.96  tff(c_4166, plain, (r1_tarski(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_3923, c_36])).
% 17.45/8.96  tff(c_263, plain, (![A_149]: (k2_xboole_0(k1_relat_1(A_149), k2_relat_1(A_149))=k3_relat_1(A_149) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.45/8.96  tff(c_22, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.45/8.96  tff(c_269, plain, (![A_12, A_149]: (r1_tarski(A_12, k3_relat_1(A_149)) | ~r1_tarski(A_12, k2_relat_1(A_149)) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_263, c_22])).
% 17.45/8.96  tff(c_1672, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1640])).
% 17.45/8.96  tff(c_76, plain, (![A_104, B_106]: (r1_tarski(k6_subset_1(k1_relat_1(A_104), k1_relat_1(B_106)), k1_relat_1(k6_subset_1(A_104, B_106))) | ~v1_relat_1(B_106) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_170])).
% 17.45/8.96  tff(c_2207, plain, (![A_260, B_261]: (r1_tarski(k4_xboole_0(k1_relat_1(A_260), k1_relat_1(B_261)), k1_relat_1(k4_xboole_0(A_260, B_261))) | ~v1_relat_1(B_261) | ~v1_relat_1(A_260))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_76])).
% 17.45/8.96  tff(c_2260, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_127, c_2207])).
% 17.45/8.96  tff(c_2287, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_1672, c_2260])).
% 17.45/8.96  tff(c_2301, plain, (k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2287, c_216])).
% 17.45/8.96  tff(c_2318, plain, (k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_126, c_2301])).
% 17.45/8.96  tff(c_3921, plain, (k2_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))=k1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_2318, c_3871])).
% 17.45/8.96  tff(c_4078, plain, (r1_tarski(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_3921, c_36])).
% 17.45/8.96  tff(c_275, plain, (![A_149]: (r1_tarski(k1_relat_1(A_149), k3_relat_1(A_149)) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_263, c_36])).
% 17.45/8.96  tff(c_719, plain, (![A_195, C_196, B_197]: (r1_tarski(k2_xboole_0(A_195, C_196), B_197) | ~r1_tarski(C_196, B_197) | ~r1_tarski(A_195, B_197))), inference(cnfTransformation, [status(thm)], [f_95])).
% 17.45/8.96  tff(c_217, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(k2_xboole_0(A_24, B_25), A_24))), inference(resolution, [status(thm)], [c_36, c_202])).
% 17.45/8.96  tff(c_735, plain, (![B_197, C_196]: (k2_xboole_0(B_197, C_196)=B_197 | ~r1_tarski(C_196, B_197) | ~r1_tarski(B_197, B_197))), inference(resolution, [status(thm)], [c_719, c_217])).
% 17.45/8.96  tff(c_763, plain, (![B_198, C_199]: (k2_xboole_0(B_198, C_199)=B_198 | ~r1_tarski(C_199, B_198))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_735])).
% 17.45/8.96  tff(c_1463, plain, (![A_239]: (k2_xboole_0(k3_relat_1(A_239), k1_relat_1(A_239))=k3_relat_1(A_239) | ~v1_relat_1(A_239))), inference(resolution, [status(thm)], [c_275, c_763])).
% 17.45/8.96  tff(c_49624, plain, (![A_825, A_826]: (r1_tarski(A_825, k3_relat_1(A_826)) | ~r1_tarski(A_825, k1_relat_1(A_826)) | ~v1_relat_1(A_826))), inference(superposition, [status(thm), theory('equality')], [c_1463, c_22])).
% 17.45/8.96  tff(c_74, plain, (![A_103]: (k2_xboole_0(k1_relat_1(A_103), k2_relat_1(A_103))=k3_relat_1(A_103) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.45/8.96  tff(c_12043, plain, (![A_411, B_412]: (r1_tarski(k3_relat_1(A_411), B_412) | ~r1_tarski(k2_relat_1(A_411), B_412) | ~r1_tarski(k1_relat_1(A_411), B_412) | ~v1_relat_1(A_411))), inference(superposition, [status(thm), theory('equality')], [c_74, c_719])).
% 17.45/8.96  tff(c_82, plain, (~r1_tarski(k3_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 17.45/8.96  tff(c_12145, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_12043, c_82])).
% 17.45/8.96  tff(c_12184, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_12145])).
% 17.45/8.96  tff(c_12207, plain, (~r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_12184])).
% 17.45/8.96  tff(c_49658, plain, (~r1_tarski(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_49624, c_12207])).
% 17.45/8.96  tff(c_49710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_4078, c_49658])).
% 17.45/8.96  tff(c_49711, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(splitRight, [status(thm)], [c_12184])).
% 17.45/8.96  tff(c_49715, plain, (~r1_tarski(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_269, c_49711])).
% 17.45/8.96  tff(c_49725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_4166, c_49715])).
% 17.45/8.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.45/8.96  
% 17.45/8.96  Inference rules
% 17.45/8.96  ----------------------
% 17.45/8.96  #Ref     : 0
% 17.45/8.96  #Sup     : 12493
% 17.45/8.96  #Fact    : 0
% 17.45/8.96  #Define  : 0
% 17.45/8.96  #Split   : 21
% 17.45/8.96  #Chain   : 0
% 17.45/8.96  #Close   : 0
% 17.45/8.96  
% 17.45/8.96  Ordering : KBO
% 17.45/8.96  
% 17.45/8.96  Simplification rules
% 17.45/8.96  ----------------------
% 17.45/8.96  #Subsume      : 3481
% 17.45/8.96  #Demod        : 8399
% 17.45/8.96  #Tautology    : 4937
% 17.45/8.96  #SimpNegUnit  : 9
% 17.45/8.96  #BackRed      : 6
% 17.45/8.96  
% 17.45/8.96  #Partial instantiations: 0
% 17.45/8.96  #Strategies tried      : 1
% 17.45/8.96  
% 17.45/8.96  Timing (in seconds)
% 17.45/8.96  ----------------------
% 17.45/8.97  Preprocessing        : 0.36
% 17.45/8.97  Parsing              : 0.19
% 17.45/8.97  CNF conversion       : 0.03
% 17.45/8.97  Main loop            : 7.83
% 17.45/8.97  Inferencing          : 1.22
% 17.45/8.97  Reduction            : 3.56
% 17.45/8.97  Demodulation         : 2.86
% 17.45/8.97  BG Simplification    : 0.13
% 17.45/8.97  Subsumption          : 2.52
% 17.45/8.97  Abstraction          : 0.17
% 17.45/8.97  MUC search           : 0.00
% 17.45/8.97  Cooper               : 0.00
% 17.45/8.97  Total                : 8.24
% 17.45/8.97  Index Insertion      : 0.00
% 17.45/8.97  Index Deletion       : 0.00
% 17.45/8.97  Index Matching       : 0.00
% 17.45/8.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
