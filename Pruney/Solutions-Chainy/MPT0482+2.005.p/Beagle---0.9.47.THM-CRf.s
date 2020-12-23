%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:31 EST 2020

% Result     : Theorem 34.95s
% Output     : CNFRefutation 34.95s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 205 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  264 ( 739 expanded)
%              Number of equality atoms :   42 ( 103 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k1_relat_1(B),A)
         => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

tff(c_34,plain,(
    k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k5_relat_1(A_23,B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_38] : r1_tarski(A_38,A_38) ),
    inference(resolution,[status(thm)],[c_42,c_4])).

tff(c_143,plain,(
    ! [A_94,B_95] :
      ( r2_hidden(k4_tarski('#skF_2'(A_94,B_95),'#skF_3'(A_94,B_95)),B_95)
      | r2_hidden(k4_tarski('#skF_4'(A_94,B_95),'#skF_5'(A_94,B_95)),A_94)
      | B_95 = A_94
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_652,plain,(
    ! [A_169,B_170,B_171] :
      ( r2_hidden(k4_tarski('#skF_2'(A_169,B_170),'#skF_3'(A_169,B_170)),B_171)
      | ~ r1_tarski(B_170,B_171)
      | r2_hidden(k4_tarski('#skF_4'(A_169,B_170),'#skF_5'(A_169,B_170)),A_169)
      | B_170 = A_169
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_169) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_12,plain,(
    ! [A_6,B_16] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_6,B_16),'#skF_3'(A_6,B_16)),A_6)
      | r2_hidden(k4_tarski('#skF_4'(A_6,B_16),'#skF_5'(A_6,B_16)),A_6)
      | B_16 = A_6
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_728,plain,(
    ! [B_172,B_173] :
      ( ~ r1_tarski(B_172,B_173)
      | r2_hidden(k4_tarski('#skF_4'(B_173,B_172),'#skF_5'(B_173,B_172)),B_173)
      | B_173 = B_172
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(B_173) ) ),
    inference(resolution,[status(thm)],[c_652,c_12])).

tff(c_26,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k1_relat_1(C_28))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_776,plain,(
    ! [B_176,B_177] :
      ( r2_hidden('#skF_4'(B_176,B_177),k1_relat_1(B_176))
      | ~ r1_tarski(B_177,B_176)
      | B_177 = B_176
      | ~ v1_relat_1(B_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_728,c_26])).

tff(c_784,plain,(
    ! [B_181,B_182,B_183] :
      ( r2_hidden('#skF_4'(B_181,B_182),B_183)
      | ~ r1_tarski(k1_relat_1(B_181),B_183)
      | ~ r1_tarski(B_182,B_181)
      | B_182 = B_181
      | ~ v1_relat_1(B_182)
      | ~ v1_relat_1(B_181) ) ),
    inference(resolution,[status(thm)],[c_776,c_2])).

tff(c_875,plain,(
    ! [B_198,B_199,B_200,B_201] :
      ( r2_hidden('#skF_4'(B_198,B_199),B_200)
      | ~ r1_tarski(B_201,B_200)
      | ~ r1_tarski(k1_relat_1(B_198),B_201)
      | ~ r1_tarski(B_199,B_198)
      | B_199 = B_198
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_784,c_2])).

tff(c_882,plain,(
    ! [B_202,B_203] :
      ( r2_hidden('#skF_4'(B_202,B_203),'#skF_6')
      | ~ r1_tarski(k1_relat_1(B_202),k1_relat_1('#skF_7'))
      | ~ r1_tarski(B_203,B_202)
      | B_203 = B_202
      | ~ v1_relat_1(B_203)
      | ~ v1_relat_1(B_202) ) ),
    inference(resolution,[status(thm)],[c_36,c_875])).

tff(c_885,plain,(
    ! [B_203] :
      ( r2_hidden('#skF_4'('#skF_7',B_203),'#skF_6')
      | ~ r1_tarski(B_203,'#skF_7')
      | B_203 = '#skF_7'
      | ~ v1_relat_1(B_203)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_47,c_882])).

tff(c_888,plain,(
    ! [B_203] :
      ( r2_hidden('#skF_4'('#skF_7',B_203),'#skF_6')
      | ~ r1_tarski(B_203,'#skF_7')
      | B_203 = '#skF_7'
      | ~ v1_relat_1(B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_885])).

tff(c_30,plain,(
    ! [A_29,B_30,D_32,C_31] :
      ( r2_hidden(k4_tarski(A_29,B_30),D_32)
      | ~ r2_hidden(k4_tarski(A_29,B_30),k5_relat_1(k6_relat_1(C_31),D_32))
      | ~ v1_relat_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1300,plain,(
    ! [A_301,C_302,D_303] :
      ( r2_hidden(k4_tarski('#skF_2'(A_301,k5_relat_1(k6_relat_1(C_302),D_303)),'#skF_3'(A_301,k5_relat_1(k6_relat_1(C_302),D_303))),D_303)
      | ~ v1_relat_1(D_303)
      | r2_hidden(k4_tarski('#skF_4'(A_301,k5_relat_1(k6_relat_1(C_302),D_303)),'#skF_5'(A_301,k5_relat_1(k6_relat_1(C_302),D_303))),A_301)
      | k5_relat_1(k6_relat_1(C_302),D_303) = A_301
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_302),D_303))
      | ~ v1_relat_1(A_301) ) ),
    inference(resolution,[status(thm)],[c_143,c_30])).

tff(c_1364,plain,(
    ! [D_303,C_302] :
      ( r2_hidden(k4_tarski('#skF_4'(D_303,k5_relat_1(k6_relat_1(C_302),D_303)),'#skF_5'(D_303,k5_relat_1(k6_relat_1(C_302),D_303))),D_303)
      | k5_relat_1(k6_relat_1(C_302),D_303) = D_303
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_302),D_303))
      | ~ v1_relat_1(D_303) ) ),
    inference(resolution,[status(thm)],[c_1300,c_12])).

tff(c_28,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( r2_hidden(k4_tarski(A_29,B_30),k5_relat_1(k6_relat_1(C_31),D_32))
      | ~ r2_hidden(k4_tarski(A_29,B_30),D_32)
      | ~ r2_hidden(A_29,C_31)
      | ~ v1_relat_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_380,plain,(
    ! [A_116,B_117] :
      ( r2_hidden(k4_tarski('#skF_2'(A_116,B_117),'#skF_3'(A_116,B_117)),B_117)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_116,B_117),'#skF_5'(A_116,B_117)),B_117)
      | B_117 = A_116
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_29,C_31,B_30,D_32] :
      ( r2_hidden(A_29,C_31)
      | ~ r2_hidden(k4_tarski(A_29,B_30),k5_relat_1(k6_relat_1(C_31),D_32))
      | ~ v1_relat_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1178,plain,(
    ! [A_281,C_282,D_283] :
      ( r2_hidden('#skF_2'(A_281,k5_relat_1(k6_relat_1(C_282),D_283)),C_282)
      | ~ v1_relat_1(D_283)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_281,k5_relat_1(k6_relat_1(C_282),D_283)),'#skF_5'(A_281,k5_relat_1(k6_relat_1(C_282),D_283))),k5_relat_1(k6_relat_1(C_282),D_283))
      | k5_relat_1(k6_relat_1(C_282),D_283) = A_281
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_282),D_283))
      | ~ v1_relat_1(A_281) ) ),
    inference(resolution,[status(thm)],[c_380,c_32])).

tff(c_12575,plain,(
    ! [A_2449,C_2450,D_2451] :
      ( r2_hidden('#skF_2'(A_2449,k5_relat_1(k6_relat_1(C_2450),D_2451)),C_2450)
      | k5_relat_1(k6_relat_1(C_2450),D_2451) = A_2449
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_2450),D_2451))
      | ~ v1_relat_1(A_2449)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_2449,k5_relat_1(k6_relat_1(C_2450),D_2451)),'#skF_5'(A_2449,k5_relat_1(k6_relat_1(C_2450),D_2451))),D_2451)
      | ~ r2_hidden('#skF_4'(A_2449,k5_relat_1(k6_relat_1(C_2450),D_2451)),C_2450)
      | ~ v1_relat_1(D_2451) ) ),
    inference(resolution,[status(thm)],[c_28,c_1178])).

tff(c_12885,plain,(
    ! [D_2452,C_2453] :
      ( r2_hidden('#skF_2'(D_2452,k5_relat_1(k6_relat_1(C_2453),D_2452)),C_2453)
      | ~ r2_hidden('#skF_4'(D_2452,k5_relat_1(k6_relat_1(C_2453),D_2452)),C_2453)
      | k5_relat_1(k6_relat_1(C_2453),D_2452) = D_2452
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_2453),D_2452))
      | ~ v1_relat_1(D_2452) ) ),
    inference(resolution,[status(thm)],[c_1364,c_12575])).

tff(c_12897,plain,(
    ! [D_2458,C_2459,B_2460] :
      ( r2_hidden('#skF_2'(D_2458,k5_relat_1(k6_relat_1(C_2459),D_2458)),B_2460)
      | ~ r1_tarski(C_2459,B_2460)
      | ~ r2_hidden('#skF_4'(D_2458,k5_relat_1(k6_relat_1(C_2459),D_2458)),C_2459)
      | k5_relat_1(k6_relat_1(C_2459),D_2458) = D_2458
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_2459),D_2458))
      | ~ v1_relat_1(D_2458) ) ),
    inference(resolution,[status(thm)],[c_12885,c_2])).

tff(c_13115,plain,(
    ! [B_2460] :
      ( r2_hidden('#skF_2'('#skF_7',k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')),B_2460)
      | ~ r1_tarski('#skF_6',B_2460)
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7'),'#skF_7')
      | k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
      | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_888,c_12897])).

tff(c_13202,plain,(
    ! [B_2460] :
      ( r2_hidden('#skF_2'('#skF_7',k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')),B_2460)
      | ~ r1_tarski('#skF_6',B_2460)
      | ~ r1_tarski(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7'),'#skF_7')
      | k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
      | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_13115])).

tff(c_13203,plain,(
    ! [B_2460] :
      ( r2_hidden('#skF_2'('#skF_7',k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')),B_2460)
      | ~ r1_tarski('#skF_6',B_2460)
      | ~ r1_tarski(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7'),'#skF_7')
      | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_13202])).

tff(c_13209,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_13203])).

tff(c_13212,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1(k6_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_20,c_13209])).

tff(c_13216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_38,c_13212])).

tff(c_13218,plain,(
    v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13203])).

tff(c_352,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114,B_115),k1_relat_1(B_115))
      | r2_hidden(k4_tarski('#skF_4'(A_114,B_115),'#skF_5'(A_114,B_115)),A_114)
      | B_115 = A_114
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_143,c_26])).

tff(c_9347,plain,(
    ! [C_1802,D_1803,B_1804] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_1802),D_1803),B_1804),'#skF_5'(k5_relat_1(k6_relat_1(C_1802),D_1803),B_1804)),D_1803)
      | ~ v1_relat_1(D_1803)
      | r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_1802),D_1803),B_1804),k1_relat_1(B_1804))
      | k5_relat_1(k6_relat_1(C_1802),D_1803) = B_1804
      | ~ v1_relat_1(B_1804)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_1802),D_1803)) ) ),
    inference(resolution,[status(thm)],[c_352,c_30])).

tff(c_417,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_2'(A_116,B_117),k1_relat_1(B_117))
      | ~ r2_hidden(k4_tarski('#skF_4'(A_116,B_117),'#skF_5'(A_116,B_117)),B_117)
      | B_117 = A_116
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_380,c_26])).

tff(c_9420,plain,(
    ! [C_1805,D_1806] :
      ( r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_1805),D_1806),D_1806),k1_relat_1(D_1806))
      | k5_relat_1(k6_relat_1(C_1805),D_1806) = D_1806
      | ~ v1_relat_1(D_1806)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_1805),D_1806)) ) ),
    inference(resolution,[status(thm)],[c_9347,c_417])).

tff(c_9426,plain,(
    ! [C_1805,D_1806,B_2] :
      ( r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_1805),D_1806),D_1806),B_2)
      | ~ r1_tarski(k1_relat_1(D_1806),B_2)
      | k5_relat_1(k6_relat_1(C_1805),D_1806) = D_1806
      | ~ v1_relat_1(D_1806)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_1805),D_1806)) ) ),
    inference(resolution,[status(thm)],[c_9420,c_2])).

tff(c_193,plain,(
    ! [C_31,D_32,B_95] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_31),D_32),B_95),'#skF_5'(k5_relat_1(k6_relat_1(C_31),D_32),B_95)),D_32)
      | ~ v1_relat_1(D_32)
      | r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_31),D_32),B_95),'#skF_3'(k5_relat_1(k6_relat_1(C_31),D_32),B_95)),B_95)
      | k5_relat_1(k6_relat_1(C_31),D_32) = B_95
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_31),D_32)) ) ),
    inference(resolution,[status(thm)],[c_143,c_30])).

tff(c_198,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_96,B_97),'#skF_3'(A_96,B_97)),A_96)
      | r2_hidden(k4_tarski('#skF_4'(A_96,B_97),'#skF_5'(A_96,B_97)),A_96)
      | B_97 = A_96
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1865,plain,(
    ! [C_391,D_392,B_393] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_391),D_392),B_393),'#skF_5'(k5_relat_1(k6_relat_1(C_391),D_392),B_393)),k5_relat_1(k6_relat_1(C_391),D_392))
      | k5_relat_1(k6_relat_1(C_391),D_392) = B_393
      | ~ v1_relat_1(B_393)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_391),D_392))
      | ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_391),D_392),B_393),'#skF_3'(k5_relat_1(k6_relat_1(C_391),D_392),B_393)),D_392)
      | ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_391),D_392),B_393),C_391)
      | ~ v1_relat_1(D_392) ) ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_17651,plain,(
    ! [C_2830,D_2831,B_2832] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_2830),D_2831),B_2832),'#skF_5'(k5_relat_1(k6_relat_1(C_2830),D_2831),B_2832)),D_2831)
      | k5_relat_1(k6_relat_1(C_2830),D_2831) = B_2832
      | ~ v1_relat_1(B_2832)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_2830),D_2831))
      | ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_2830),D_2831),B_2832),'#skF_3'(k5_relat_1(k6_relat_1(C_2830),D_2831),B_2832)),D_2831)
      | ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_2830),D_2831),B_2832),C_2830)
      | ~ v1_relat_1(D_2831) ) ),
    inference(resolution,[status(thm)],[c_1865,c_30])).

tff(c_17945,plain,(
    ! [C_31,B_95] :
      ( ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_31),B_95),B_95),C_31)
      | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_31),B_95),B_95),'#skF_5'(k5_relat_1(k6_relat_1(C_31),B_95),B_95)),B_95)
      | k5_relat_1(k6_relat_1(C_31),B_95) = B_95
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_31),B_95)) ) ),
    inference(resolution,[status(thm)],[c_193,c_17651])).

tff(c_10,plain,(
    ! [A_6,B_16] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6,B_16),'#skF_3'(A_6,B_16)),B_16)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_6,B_16),'#skF_5'(A_6,B_16)),B_16)
      | B_16 = A_6
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18497,plain,(
    ! [C_2924,B_2925] :
      ( ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_2924),B_2925),B_2925),C_2924)
      | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_2924),B_2925),B_2925),'#skF_5'(k5_relat_1(k6_relat_1(C_2924),B_2925),B_2925)),B_2925)
      | k5_relat_1(k6_relat_1(C_2924),B_2925) = B_2925
      | ~ v1_relat_1(B_2925)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_2924),B_2925)) ) ),
    inference(resolution,[status(thm)],[c_193,c_17651])).

tff(c_252,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_104,B_105),'#skF_3'(A_104,B_105)),A_104)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_104,B_105),'#skF_5'(A_104,B_105)),B_105)
      | B_105 = A_104
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_261,plain,(
    ! [C_31,D_32,B_105] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_31),D_32),B_105),'#skF_5'(k5_relat_1(k6_relat_1(C_31),D_32),B_105)),B_105)
      | k5_relat_1(k6_relat_1(C_31),D_32) = B_105
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_31),D_32))
      | ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_31),D_32),B_105),'#skF_3'(k5_relat_1(k6_relat_1(C_31),D_32),B_105)),D_32)
      | ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_31),D_32),B_105),C_31)
      | ~ v1_relat_1(D_32) ) ),
    inference(resolution,[status(thm)],[c_28,c_252])).

tff(c_21319,plain,(
    ! [C_3171,B_3172] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_3171),B_3172),B_3172),'#skF_3'(k5_relat_1(k6_relat_1(C_3171),B_3172),B_3172)),B_3172)
      | ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_3171),B_3172),B_3172),C_3171)
      | k5_relat_1(k6_relat_1(C_3171),B_3172) = B_3172
      | ~ v1_relat_1(B_3172)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_3171),B_3172)) ) ),
    inference(resolution,[status(thm)],[c_18497,c_261])).

tff(c_26369,plain,(
    ! [C_3356,B_3357] :
      ( ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_3356),B_3357),B_3357),C_3356)
      | ~ r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_3356),B_3357),B_3357),'#skF_5'(k5_relat_1(k6_relat_1(C_3356),B_3357),B_3357)),B_3357)
      | k5_relat_1(k6_relat_1(C_3356),B_3357) = B_3357
      | ~ v1_relat_1(B_3357)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_3356),B_3357)) ) ),
    inference(resolution,[status(thm)],[c_10,c_21319])).

tff(c_26615,plain,(
    ! [C_3358,B_3359] :
      ( ~ r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_3358),B_3359),B_3359),C_3358)
      | k5_relat_1(k6_relat_1(C_3358),B_3359) = B_3359
      | ~ v1_relat_1(B_3359)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_3358),B_3359)) ) ),
    inference(resolution,[status(thm)],[c_17945,c_26369])).

tff(c_28779,plain,(
    ! [D_3362,B_3363] :
      ( ~ r1_tarski(k1_relat_1(D_3362),B_3363)
      | k5_relat_1(k6_relat_1(B_3363),D_3362) = D_3362
      | ~ v1_relat_1(D_3362)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(B_3363),D_3362)) ) ),
    inference(resolution,[status(thm)],[c_9426,c_26615])).

tff(c_28785,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_13218,c_28779])).

tff(c_28794,plain,(
    k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_28785])).

tff(c_28796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_28794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.95/25.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.95/25.42  
% 34.95/25.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.95/25.43  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 34.95/25.43  
% 34.95/25.43  %Foreground sorts:
% 34.95/25.43  
% 34.95/25.43  
% 34.95/25.43  %Background operators:
% 34.95/25.43  
% 34.95/25.43  
% 34.95/25.43  %Foreground operators:
% 34.95/25.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.95/25.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 34.95/25.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 34.95/25.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 34.95/25.43  tff('#skF_7', type, '#skF_7': $i).
% 34.95/25.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 34.95/25.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.95/25.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.95/25.43  tff('#skF_6', type, '#skF_6': $i).
% 34.95/25.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.95/25.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.95/25.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 34.95/25.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.95/25.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 34.95/25.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 34.95/25.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 34.95/25.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.95/25.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 34.95/25.43  
% 34.95/25.44  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 34.95/25.44  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 34.95/25.44  tff(f_50, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 34.95/25.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 34.95/25.44  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_relat_1)).
% 34.95/25.44  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 34.95/25.44  tff(f_68, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 34.95/25.44  tff(c_34, plain, (k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.95/25.44  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.95/25.44  tff(c_36, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.95/25.44  tff(c_22, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 34.95/25.44  tff(c_20, plain, (![A_23, B_24]: (v1_relat_1(k5_relat_1(A_23, B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 34.95/25.44  tff(c_42, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.95/25.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.95/25.44  tff(c_47, plain, (![A_38]: (r1_tarski(A_38, A_38))), inference(resolution, [status(thm)], [c_42, c_4])).
% 34.95/25.44  tff(c_143, plain, (![A_94, B_95]: (r2_hidden(k4_tarski('#skF_2'(A_94, B_95), '#skF_3'(A_94, B_95)), B_95) | r2_hidden(k4_tarski('#skF_4'(A_94, B_95), '#skF_5'(A_94, B_95)), A_94) | B_95=A_94 | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_44])).
% 34.95/25.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.95/25.44  tff(c_652, plain, (![A_169, B_170, B_171]: (r2_hidden(k4_tarski('#skF_2'(A_169, B_170), '#skF_3'(A_169, B_170)), B_171) | ~r1_tarski(B_170, B_171) | r2_hidden(k4_tarski('#skF_4'(A_169, B_170), '#skF_5'(A_169, B_170)), A_169) | B_170=A_169 | ~v1_relat_1(B_170) | ~v1_relat_1(A_169))), inference(resolution, [status(thm)], [c_143, c_2])).
% 34.95/25.44  tff(c_12, plain, (![A_6, B_16]: (~r2_hidden(k4_tarski('#skF_2'(A_6, B_16), '#skF_3'(A_6, B_16)), A_6) | r2_hidden(k4_tarski('#skF_4'(A_6, B_16), '#skF_5'(A_6, B_16)), A_6) | B_16=A_6 | ~v1_relat_1(B_16) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 34.95/25.44  tff(c_728, plain, (![B_172, B_173]: (~r1_tarski(B_172, B_173) | r2_hidden(k4_tarski('#skF_4'(B_173, B_172), '#skF_5'(B_173, B_172)), B_173) | B_173=B_172 | ~v1_relat_1(B_172) | ~v1_relat_1(B_173))), inference(resolution, [status(thm)], [c_652, c_12])).
% 34.95/25.44  tff(c_26, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k1_relat_1(C_28)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 34.95/25.44  tff(c_776, plain, (![B_176, B_177]: (r2_hidden('#skF_4'(B_176, B_177), k1_relat_1(B_176)) | ~r1_tarski(B_177, B_176) | B_177=B_176 | ~v1_relat_1(B_177) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_728, c_26])).
% 34.95/25.44  tff(c_784, plain, (![B_181, B_182, B_183]: (r2_hidden('#skF_4'(B_181, B_182), B_183) | ~r1_tarski(k1_relat_1(B_181), B_183) | ~r1_tarski(B_182, B_181) | B_182=B_181 | ~v1_relat_1(B_182) | ~v1_relat_1(B_181))), inference(resolution, [status(thm)], [c_776, c_2])).
% 34.95/25.44  tff(c_875, plain, (![B_198, B_199, B_200, B_201]: (r2_hidden('#skF_4'(B_198, B_199), B_200) | ~r1_tarski(B_201, B_200) | ~r1_tarski(k1_relat_1(B_198), B_201) | ~r1_tarski(B_199, B_198) | B_199=B_198 | ~v1_relat_1(B_199) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_784, c_2])).
% 34.95/25.44  tff(c_882, plain, (![B_202, B_203]: (r2_hidden('#skF_4'(B_202, B_203), '#skF_6') | ~r1_tarski(k1_relat_1(B_202), k1_relat_1('#skF_7')) | ~r1_tarski(B_203, B_202) | B_203=B_202 | ~v1_relat_1(B_203) | ~v1_relat_1(B_202))), inference(resolution, [status(thm)], [c_36, c_875])).
% 34.95/25.44  tff(c_885, plain, (![B_203]: (r2_hidden('#skF_4'('#skF_7', B_203), '#skF_6') | ~r1_tarski(B_203, '#skF_7') | B_203='#skF_7' | ~v1_relat_1(B_203) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_47, c_882])).
% 34.95/25.44  tff(c_888, plain, (![B_203]: (r2_hidden('#skF_4'('#skF_7', B_203), '#skF_6') | ~r1_tarski(B_203, '#skF_7') | B_203='#skF_7' | ~v1_relat_1(B_203))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_885])).
% 34.95/25.44  tff(c_30, plain, (![A_29, B_30, D_32, C_31]: (r2_hidden(k4_tarski(A_29, B_30), D_32) | ~r2_hidden(k4_tarski(A_29, B_30), k5_relat_1(k6_relat_1(C_31), D_32)) | ~v1_relat_1(D_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.95/25.44  tff(c_1300, plain, (![A_301, C_302, D_303]: (r2_hidden(k4_tarski('#skF_2'(A_301, k5_relat_1(k6_relat_1(C_302), D_303)), '#skF_3'(A_301, k5_relat_1(k6_relat_1(C_302), D_303))), D_303) | ~v1_relat_1(D_303) | r2_hidden(k4_tarski('#skF_4'(A_301, k5_relat_1(k6_relat_1(C_302), D_303)), '#skF_5'(A_301, k5_relat_1(k6_relat_1(C_302), D_303))), A_301) | k5_relat_1(k6_relat_1(C_302), D_303)=A_301 | ~v1_relat_1(k5_relat_1(k6_relat_1(C_302), D_303)) | ~v1_relat_1(A_301))), inference(resolution, [status(thm)], [c_143, c_30])).
% 34.95/25.44  tff(c_1364, plain, (![D_303, C_302]: (r2_hidden(k4_tarski('#skF_4'(D_303, k5_relat_1(k6_relat_1(C_302), D_303)), '#skF_5'(D_303, k5_relat_1(k6_relat_1(C_302), D_303))), D_303) | k5_relat_1(k6_relat_1(C_302), D_303)=D_303 | ~v1_relat_1(k5_relat_1(k6_relat_1(C_302), D_303)) | ~v1_relat_1(D_303))), inference(resolution, [status(thm)], [c_1300, c_12])).
% 34.95/25.44  tff(c_28, plain, (![A_29, B_30, C_31, D_32]: (r2_hidden(k4_tarski(A_29, B_30), k5_relat_1(k6_relat_1(C_31), D_32)) | ~r2_hidden(k4_tarski(A_29, B_30), D_32) | ~r2_hidden(A_29, C_31) | ~v1_relat_1(D_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.95/25.44  tff(c_380, plain, (![A_116, B_117]: (r2_hidden(k4_tarski('#skF_2'(A_116, B_117), '#skF_3'(A_116, B_117)), B_117) | ~r2_hidden(k4_tarski('#skF_4'(A_116, B_117), '#skF_5'(A_116, B_117)), B_117) | B_117=A_116 | ~v1_relat_1(B_117) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_44])).
% 34.95/25.44  tff(c_32, plain, (![A_29, C_31, B_30, D_32]: (r2_hidden(A_29, C_31) | ~r2_hidden(k4_tarski(A_29, B_30), k5_relat_1(k6_relat_1(C_31), D_32)) | ~v1_relat_1(D_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.95/25.44  tff(c_1178, plain, (![A_281, C_282, D_283]: (r2_hidden('#skF_2'(A_281, k5_relat_1(k6_relat_1(C_282), D_283)), C_282) | ~v1_relat_1(D_283) | ~r2_hidden(k4_tarski('#skF_4'(A_281, k5_relat_1(k6_relat_1(C_282), D_283)), '#skF_5'(A_281, k5_relat_1(k6_relat_1(C_282), D_283))), k5_relat_1(k6_relat_1(C_282), D_283)) | k5_relat_1(k6_relat_1(C_282), D_283)=A_281 | ~v1_relat_1(k5_relat_1(k6_relat_1(C_282), D_283)) | ~v1_relat_1(A_281))), inference(resolution, [status(thm)], [c_380, c_32])).
% 34.95/25.44  tff(c_12575, plain, (![A_2449, C_2450, D_2451]: (r2_hidden('#skF_2'(A_2449, k5_relat_1(k6_relat_1(C_2450), D_2451)), C_2450) | k5_relat_1(k6_relat_1(C_2450), D_2451)=A_2449 | ~v1_relat_1(k5_relat_1(k6_relat_1(C_2450), D_2451)) | ~v1_relat_1(A_2449) | ~r2_hidden(k4_tarski('#skF_4'(A_2449, k5_relat_1(k6_relat_1(C_2450), D_2451)), '#skF_5'(A_2449, k5_relat_1(k6_relat_1(C_2450), D_2451))), D_2451) | ~r2_hidden('#skF_4'(A_2449, k5_relat_1(k6_relat_1(C_2450), D_2451)), C_2450) | ~v1_relat_1(D_2451))), inference(resolution, [status(thm)], [c_28, c_1178])).
% 34.95/25.44  tff(c_12885, plain, (![D_2452, C_2453]: (r2_hidden('#skF_2'(D_2452, k5_relat_1(k6_relat_1(C_2453), D_2452)), C_2453) | ~r2_hidden('#skF_4'(D_2452, k5_relat_1(k6_relat_1(C_2453), D_2452)), C_2453) | k5_relat_1(k6_relat_1(C_2453), D_2452)=D_2452 | ~v1_relat_1(k5_relat_1(k6_relat_1(C_2453), D_2452)) | ~v1_relat_1(D_2452))), inference(resolution, [status(thm)], [c_1364, c_12575])).
% 34.95/25.44  tff(c_12897, plain, (![D_2458, C_2459, B_2460]: (r2_hidden('#skF_2'(D_2458, k5_relat_1(k6_relat_1(C_2459), D_2458)), B_2460) | ~r1_tarski(C_2459, B_2460) | ~r2_hidden('#skF_4'(D_2458, k5_relat_1(k6_relat_1(C_2459), D_2458)), C_2459) | k5_relat_1(k6_relat_1(C_2459), D_2458)=D_2458 | ~v1_relat_1(k5_relat_1(k6_relat_1(C_2459), D_2458)) | ~v1_relat_1(D_2458))), inference(resolution, [status(thm)], [c_12885, c_2])).
% 34.95/25.44  tff(c_13115, plain, (![B_2460]: (r2_hidden('#skF_2'('#skF_7', k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')), B_2460) | ~r1_tarski('#skF_6', B_2460) | ~v1_relat_1('#skF_7') | ~r1_tarski(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7'), '#skF_7') | k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7' | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')))), inference(resolution, [status(thm)], [c_888, c_12897])).
% 34.95/25.44  tff(c_13202, plain, (![B_2460]: (r2_hidden('#skF_2'('#skF_7', k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')), B_2460) | ~r1_tarski('#skF_6', B_2460) | ~r1_tarski(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7'), '#skF_7') | k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7' | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_13115])).
% 34.95/25.44  tff(c_13203, plain, (![B_2460]: (r2_hidden('#skF_2'('#skF_7', k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')), B_2460) | ~r1_tarski('#skF_6', B_2460) | ~r1_tarski(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7'), '#skF_7') | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_34, c_13202])).
% 34.95/25.44  tff(c_13209, plain, (~v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_13203])).
% 34.95/25.44  tff(c_13212, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1(k6_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_13209])).
% 34.95/25.44  tff(c_13216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_38, c_13212])).
% 34.95/25.44  tff(c_13218, plain, (v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_13203])).
% 34.95/25.44  tff(c_352, plain, (![A_114, B_115]: (r2_hidden('#skF_2'(A_114, B_115), k1_relat_1(B_115)) | r2_hidden(k4_tarski('#skF_4'(A_114, B_115), '#skF_5'(A_114, B_115)), A_114) | B_115=A_114 | ~v1_relat_1(B_115) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_143, c_26])).
% 34.95/25.44  tff(c_9347, plain, (![C_1802, D_1803, B_1804]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_1802), D_1803), B_1804), '#skF_5'(k5_relat_1(k6_relat_1(C_1802), D_1803), B_1804)), D_1803) | ~v1_relat_1(D_1803) | r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_1802), D_1803), B_1804), k1_relat_1(B_1804)) | k5_relat_1(k6_relat_1(C_1802), D_1803)=B_1804 | ~v1_relat_1(B_1804) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_1802), D_1803)))), inference(resolution, [status(thm)], [c_352, c_30])).
% 34.95/25.44  tff(c_417, plain, (![A_116, B_117]: (r2_hidden('#skF_2'(A_116, B_117), k1_relat_1(B_117)) | ~r2_hidden(k4_tarski('#skF_4'(A_116, B_117), '#skF_5'(A_116, B_117)), B_117) | B_117=A_116 | ~v1_relat_1(B_117) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_380, c_26])).
% 34.95/25.44  tff(c_9420, plain, (![C_1805, D_1806]: (r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_1805), D_1806), D_1806), k1_relat_1(D_1806)) | k5_relat_1(k6_relat_1(C_1805), D_1806)=D_1806 | ~v1_relat_1(D_1806) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_1805), D_1806)))), inference(resolution, [status(thm)], [c_9347, c_417])).
% 34.95/25.44  tff(c_9426, plain, (![C_1805, D_1806, B_2]: (r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_1805), D_1806), D_1806), B_2) | ~r1_tarski(k1_relat_1(D_1806), B_2) | k5_relat_1(k6_relat_1(C_1805), D_1806)=D_1806 | ~v1_relat_1(D_1806) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_1805), D_1806)))), inference(resolution, [status(thm)], [c_9420, c_2])).
% 34.95/25.44  tff(c_193, plain, (![C_31, D_32, B_95]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_31), D_32), B_95), '#skF_5'(k5_relat_1(k6_relat_1(C_31), D_32), B_95)), D_32) | ~v1_relat_1(D_32) | r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_31), D_32), B_95), '#skF_3'(k5_relat_1(k6_relat_1(C_31), D_32), B_95)), B_95) | k5_relat_1(k6_relat_1(C_31), D_32)=B_95 | ~v1_relat_1(B_95) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_31), D_32)))), inference(resolution, [status(thm)], [c_143, c_30])).
% 34.95/25.44  tff(c_198, plain, (![A_96, B_97]: (~r2_hidden(k4_tarski('#skF_2'(A_96, B_97), '#skF_3'(A_96, B_97)), A_96) | r2_hidden(k4_tarski('#skF_4'(A_96, B_97), '#skF_5'(A_96, B_97)), A_96) | B_97=A_96 | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_44])).
% 34.95/25.44  tff(c_1865, plain, (![C_391, D_392, B_393]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_391), D_392), B_393), '#skF_5'(k5_relat_1(k6_relat_1(C_391), D_392), B_393)), k5_relat_1(k6_relat_1(C_391), D_392)) | k5_relat_1(k6_relat_1(C_391), D_392)=B_393 | ~v1_relat_1(B_393) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_391), D_392)) | ~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_391), D_392), B_393), '#skF_3'(k5_relat_1(k6_relat_1(C_391), D_392), B_393)), D_392) | ~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_391), D_392), B_393), C_391) | ~v1_relat_1(D_392))), inference(resolution, [status(thm)], [c_28, c_198])).
% 34.95/25.44  tff(c_17651, plain, (![C_2830, D_2831, B_2832]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_2830), D_2831), B_2832), '#skF_5'(k5_relat_1(k6_relat_1(C_2830), D_2831), B_2832)), D_2831) | k5_relat_1(k6_relat_1(C_2830), D_2831)=B_2832 | ~v1_relat_1(B_2832) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_2830), D_2831)) | ~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_2830), D_2831), B_2832), '#skF_3'(k5_relat_1(k6_relat_1(C_2830), D_2831), B_2832)), D_2831) | ~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_2830), D_2831), B_2832), C_2830) | ~v1_relat_1(D_2831))), inference(resolution, [status(thm)], [c_1865, c_30])).
% 34.95/25.44  tff(c_17945, plain, (![C_31, B_95]: (~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_31), B_95), B_95), C_31) | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_31), B_95), B_95), '#skF_5'(k5_relat_1(k6_relat_1(C_31), B_95), B_95)), B_95) | k5_relat_1(k6_relat_1(C_31), B_95)=B_95 | ~v1_relat_1(B_95) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_31), B_95)))), inference(resolution, [status(thm)], [c_193, c_17651])).
% 34.95/25.44  tff(c_10, plain, (![A_6, B_16]: (r2_hidden(k4_tarski('#skF_2'(A_6, B_16), '#skF_3'(A_6, B_16)), B_16) | ~r2_hidden(k4_tarski('#skF_4'(A_6, B_16), '#skF_5'(A_6, B_16)), B_16) | B_16=A_6 | ~v1_relat_1(B_16) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 34.95/25.44  tff(c_18497, plain, (![C_2924, B_2925]: (~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_2924), B_2925), B_2925), C_2924) | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_2924), B_2925), B_2925), '#skF_5'(k5_relat_1(k6_relat_1(C_2924), B_2925), B_2925)), B_2925) | k5_relat_1(k6_relat_1(C_2924), B_2925)=B_2925 | ~v1_relat_1(B_2925) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_2924), B_2925)))), inference(resolution, [status(thm)], [c_193, c_17651])).
% 34.95/25.44  tff(c_252, plain, (![A_104, B_105]: (~r2_hidden(k4_tarski('#skF_2'(A_104, B_105), '#skF_3'(A_104, B_105)), A_104) | ~r2_hidden(k4_tarski('#skF_4'(A_104, B_105), '#skF_5'(A_104, B_105)), B_105) | B_105=A_104 | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_44])).
% 34.95/25.44  tff(c_261, plain, (![C_31, D_32, B_105]: (~r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_31), D_32), B_105), '#skF_5'(k5_relat_1(k6_relat_1(C_31), D_32), B_105)), B_105) | k5_relat_1(k6_relat_1(C_31), D_32)=B_105 | ~v1_relat_1(B_105) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_31), D_32)) | ~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_31), D_32), B_105), '#skF_3'(k5_relat_1(k6_relat_1(C_31), D_32), B_105)), D_32) | ~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_31), D_32), B_105), C_31) | ~v1_relat_1(D_32))), inference(resolution, [status(thm)], [c_28, c_252])).
% 34.95/25.44  tff(c_21319, plain, (![C_3171, B_3172]: (~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(k6_relat_1(C_3171), B_3172), B_3172), '#skF_3'(k5_relat_1(k6_relat_1(C_3171), B_3172), B_3172)), B_3172) | ~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_3171), B_3172), B_3172), C_3171) | k5_relat_1(k6_relat_1(C_3171), B_3172)=B_3172 | ~v1_relat_1(B_3172) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_3171), B_3172)))), inference(resolution, [status(thm)], [c_18497, c_261])).
% 34.95/25.44  tff(c_26369, plain, (![C_3356, B_3357]: (~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_3356), B_3357), B_3357), C_3356) | ~r2_hidden(k4_tarski('#skF_4'(k5_relat_1(k6_relat_1(C_3356), B_3357), B_3357), '#skF_5'(k5_relat_1(k6_relat_1(C_3356), B_3357), B_3357)), B_3357) | k5_relat_1(k6_relat_1(C_3356), B_3357)=B_3357 | ~v1_relat_1(B_3357) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_3356), B_3357)))), inference(resolution, [status(thm)], [c_10, c_21319])).
% 34.95/25.44  tff(c_26615, plain, (![C_3358, B_3359]: (~r2_hidden('#skF_2'(k5_relat_1(k6_relat_1(C_3358), B_3359), B_3359), C_3358) | k5_relat_1(k6_relat_1(C_3358), B_3359)=B_3359 | ~v1_relat_1(B_3359) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_3358), B_3359)))), inference(resolution, [status(thm)], [c_17945, c_26369])).
% 34.95/25.44  tff(c_28779, plain, (![D_3362, B_3363]: (~r1_tarski(k1_relat_1(D_3362), B_3363) | k5_relat_1(k6_relat_1(B_3363), D_3362)=D_3362 | ~v1_relat_1(D_3362) | ~v1_relat_1(k5_relat_1(k6_relat_1(B_3363), D_3362)))), inference(resolution, [status(thm)], [c_9426, c_26615])).
% 34.95/25.44  tff(c_28785, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_13218, c_28779])).
% 34.95/25.44  tff(c_28794, plain, (k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_28785])).
% 34.95/25.44  tff(c_28796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_28794])).
% 34.95/25.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.95/25.44  
% 34.95/25.44  Inference rules
% 34.95/25.44  ----------------------
% 34.95/25.44  #Ref     : 0
% 34.95/25.44  #Sup     : 6898
% 34.95/25.44  #Fact    : 6
% 34.95/25.44  #Define  : 0
% 34.95/25.44  #Split   : 12
% 34.95/25.44  #Chain   : 0
% 34.95/25.44  #Close   : 0
% 34.95/25.44  
% 34.95/25.44  Ordering : KBO
% 34.95/25.44  
% 34.95/25.44  Simplification rules
% 34.95/25.44  ----------------------
% 34.95/25.44  #Subsume      : 2081
% 34.95/25.44  #Demod        : 285
% 34.95/25.44  #Tautology    : 289
% 34.95/25.44  #SimpNegUnit  : 28
% 34.95/25.44  #BackRed      : 0
% 34.95/25.45  
% 34.95/25.45  #Partial instantiations: 0
% 34.95/25.45  #Strategies tried      : 1
% 34.95/25.45  
% 34.95/25.45  Timing (in seconds)
% 34.95/25.45  ----------------------
% 34.95/25.45  Preprocessing        : 0.31
% 34.95/25.45  Parsing              : 0.17
% 34.95/25.45  CNF conversion       : 0.02
% 34.95/25.45  Main loop            : 24.31
% 34.95/25.45  Inferencing          : 5.88
% 34.95/25.45  Reduction            : 3.81
% 34.95/25.45  Demodulation         : 2.64
% 34.95/25.45  BG Simplification    : 0.23
% 34.95/25.45  Subsumption          : 13.54
% 34.95/25.45  Abstraction          : 0.37
% 34.95/25.45  MUC search           : 0.00
% 34.95/25.45  Cooper               : 0.00
% 34.95/25.45  Total                : 24.66
% 34.95/25.45  Index Insertion      : 0.00
% 34.95/25.45  Index Deletion       : 0.00
% 34.95/25.45  Index Matching       : 0.00
% 34.95/25.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
