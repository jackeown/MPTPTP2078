%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:32 EST 2020

% Result     : Theorem 30.27s
% Output     : CNFRefutation 30.43s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 214 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 ( 768 expanded)
%              Number of equality atoms :   44 ( 105 expanded)
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
       => ( r1_tarski(k2_relat_1(B),A)
         => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
      <=> ( r2_hidden(B,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

tff(c_34,plain,(
    k5_relat_1('#skF_7',k6_relat_1('#skF_6')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
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

tff(c_36,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

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
    ! [A_166,B_167,B_168] :
      ( r2_hidden(k4_tarski('#skF_2'(A_166,B_167),'#skF_3'(A_166,B_167)),B_168)
      | ~ r1_tarski(B_167,B_168)
      | r2_hidden(k4_tarski('#skF_4'(A_166,B_167),'#skF_5'(A_166,B_167)),A_166)
      | B_167 = A_166
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(A_166) ) ),
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
    ! [B_169,B_170] :
      ( ~ r1_tarski(B_169,B_170)
      | r2_hidden(k4_tarski('#skF_4'(B_170,B_169),'#skF_5'(B_170,B_169)),B_170)
      | B_170 = B_169
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_652,c_12])).

tff(c_24,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k2_relat_1(C_28))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_772,plain,(
    ! [B_171,B_172] :
      ( r2_hidden('#skF_5'(B_171,B_172),k2_relat_1(B_171))
      | ~ r1_tarski(B_172,B_171)
      | B_172 = B_171
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(B_171) ) ),
    inference(resolution,[status(thm)],[c_728,c_24])).

tff(c_787,plain,(
    ! [B_178,B_179,B_180] :
      ( r2_hidden('#skF_5'(B_178,B_179),B_180)
      | ~ r1_tarski(k2_relat_1(B_178),B_180)
      | ~ r1_tarski(B_179,B_178)
      | B_179 = B_178
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_772,c_2])).

tff(c_894,plain,(
    ! [B_207,B_208,B_209,B_210] :
      ( r2_hidden('#skF_5'(B_207,B_208),B_209)
      | ~ r1_tarski(B_210,B_209)
      | ~ r1_tarski(k2_relat_1(B_207),B_210)
      | ~ r1_tarski(B_208,B_207)
      | B_208 = B_207
      | ~ v1_relat_1(B_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_787,c_2])).

tff(c_901,plain,(
    ! [B_211,B_212] :
      ( r2_hidden('#skF_5'(B_211,B_212),'#skF_6')
      | ~ r1_tarski(k2_relat_1(B_211),k2_relat_1('#skF_7'))
      | ~ r1_tarski(B_212,B_211)
      | B_212 = B_211
      | ~ v1_relat_1(B_212)
      | ~ v1_relat_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_36,c_894])).

tff(c_904,plain,(
    ! [B_212] :
      ( r2_hidden('#skF_5'('#skF_7',B_212),'#skF_6')
      | ~ r1_tarski(B_212,'#skF_7')
      | B_212 = '#skF_7'
      | ~ v1_relat_1(B_212)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_47,c_901])).

tff(c_907,plain,(
    ! [B_212] :
      ( r2_hidden('#skF_5'('#skF_7',B_212),'#skF_6')
      | ~ r1_tarski(B_212,'#skF_7')
      | B_212 = '#skF_7'
      | ~ v1_relat_1(B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_904])).

tff(c_30,plain,(
    ! [A_29,B_30,D_32,C_31] :
      ( r2_hidden(k4_tarski(A_29,B_30),D_32)
      | ~ r2_hidden(k4_tarski(A_29,B_30),k5_relat_1(D_32,k6_relat_1(C_31)))
      | ~ v1_relat_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1300,plain,(
    ! [A_301,D_302,C_303] :
      ( r2_hidden(k4_tarski('#skF_2'(A_301,k5_relat_1(D_302,k6_relat_1(C_303))),'#skF_3'(A_301,k5_relat_1(D_302,k6_relat_1(C_303)))),D_302)
      | ~ v1_relat_1(D_302)
      | r2_hidden(k4_tarski('#skF_4'(A_301,k5_relat_1(D_302,k6_relat_1(C_303))),'#skF_5'(A_301,k5_relat_1(D_302,k6_relat_1(C_303)))),A_301)
      | k5_relat_1(D_302,k6_relat_1(C_303)) = A_301
      | ~ v1_relat_1(k5_relat_1(D_302,k6_relat_1(C_303)))
      | ~ v1_relat_1(A_301) ) ),
    inference(resolution,[status(thm)],[c_143,c_30])).

tff(c_1364,plain,(
    ! [D_302,C_303] :
      ( r2_hidden(k4_tarski('#skF_4'(D_302,k5_relat_1(D_302,k6_relat_1(C_303))),'#skF_5'(D_302,k5_relat_1(D_302,k6_relat_1(C_303)))),D_302)
      | k5_relat_1(D_302,k6_relat_1(C_303)) = D_302
      | ~ v1_relat_1(k5_relat_1(D_302,k6_relat_1(C_303)))
      | ~ v1_relat_1(D_302) ) ),
    inference(resolution,[status(thm)],[c_1300,c_12])).

tff(c_28,plain,(
    ! [A_29,B_30,D_32,C_31] :
      ( r2_hidden(k4_tarski(A_29,B_30),k5_relat_1(D_32,k6_relat_1(C_31)))
      | ~ r2_hidden(k4_tarski(A_29,B_30),D_32)
      | ~ r2_hidden(B_30,C_31)
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
    ! [B_30,C_31,A_29,D_32] :
      ( r2_hidden(B_30,C_31)
      | ~ r2_hidden(k4_tarski(A_29,B_30),k5_relat_1(D_32,k6_relat_1(C_31)))
      | ~ v1_relat_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1207,plain,(
    ! [A_278,D_279,C_280] :
      ( r2_hidden('#skF_3'(A_278,k5_relat_1(D_279,k6_relat_1(C_280))),C_280)
      | ~ v1_relat_1(D_279)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_278,k5_relat_1(D_279,k6_relat_1(C_280))),'#skF_5'(A_278,k5_relat_1(D_279,k6_relat_1(C_280)))),k5_relat_1(D_279,k6_relat_1(C_280)))
      | k5_relat_1(D_279,k6_relat_1(C_280)) = A_278
      | ~ v1_relat_1(k5_relat_1(D_279,k6_relat_1(C_280)))
      | ~ v1_relat_1(A_278) ) ),
    inference(resolution,[status(thm)],[c_380,c_32])).

tff(c_12458,plain,(
    ! [A_2453,D_2454,C_2455] :
      ( r2_hidden('#skF_3'(A_2453,k5_relat_1(D_2454,k6_relat_1(C_2455))),C_2455)
      | k5_relat_1(D_2454,k6_relat_1(C_2455)) = A_2453
      | ~ v1_relat_1(k5_relat_1(D_2454,k6_relat_1(C_2455)))
      | ~ v1_relat_1(A_2453)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_2453,k5_relat_1(D_2454,k6_relat_1(C_2455))),'#skF_5'(A_2453,k5_relat_1(D_2454,k6_relat_1(C_2455)))),D_2454)
      | ~ r2_hidden('#skF_5'(A_2453,k5_relat_1(D_2454,k6_relat_1(C_2455))),C_2455)
      | ~ v1_relat_1(D_2454) ) ),
    inference(resolution,[status(thm)],[c_28,c_1207])).

tff(c_12768,plain,(
    ! [D_2456,C_2457] :
      ( r2_hidden('#skF_3'(D_2456,k5_relat_1(D_2456,k6_relat_1(C_2457))),C_2457)
      | ~ r2_hidden('#skF_5'(D_2456,k5_relat_1(D_2456,k6_relat_1(C_2457))),C_2457)
      | k5_relat_1(D_2456,k6_relat_1(C_2457)) = D_2456
      | ~ v1_relat_1(k5_relat_1(D_2456,k6_relat_1(C_2457)))
      | ~ v1_relat_1(D_2456) ) ),
    inference(resolution,[status(thm)],[c_1364,c_12458])).

tff(c_12780,plain,(
    ! [D_2462,C_2463,B_2464] :
      ( r2_hidden('#skF_3'(D_2462,k5_relat_1(D_2462,k6_relat_1(C_2463))),B_2464)
      | ~ r1_tarski(C_2463,B_2464)
      | ~ r2_hidden('#skF_5'(D_2462,k5_relat_1(D_2462,k6_relat_1(C_2463))),C_2463)
      | k5_relat_1(D_2462,k6_relat_1(C_2463)) = D_2462
      | ~ v1_relat_1(k5_relat_1(D_2462,k6_relat_1(C_2463)))
      | ~ v1_relat_1(D_2462) ) ),
    inference(resolution,[status(thm)],[c_12768,c_2])).

tff(c_12999,plain,(
    ! [B_2464] :
      ( r2_hidden('#skF_3'('#skF_7',k5_relat_1('#skF_7',k6_relat_1('#skF_6'))),B_2464)
      | ~ r1_tarski('#skF_6',B_2464)
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(k5_relat_1('#skF_7',k6_relat_1('#skF_6')),'#skF_7')
      | k5_relat_1('#skF_7',k6_relat_1('#skF_6')) = '#skF_7'
      | ~ v1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_907,c_12780])).

tff(c_13085,plain,(
    ! [B_2464] :
      ( r2_hidden('#skF_3'('#skF_7',k5_relat_1('#skF_7',k6_relat_1('#skF_6'))),B_2464)
      | ~ r1_tarski('#skF_6',B_2464)
      | ~ r1_tarski(k5_relat_1('#skF_7',k6_relat_1('#skF_6')),'#skF_7')
      | k5_relat_1('#skF_7',k6_relat_1('#skF_6')) = '#skF_7'
      | ~ v1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12999])).

tff(c_13086,plain,(
    ! [B_2464] :
      ( r2_hidden('#skF_3'('#skF_7',k5_relat_1('#skF_7',k6_relat_1('#skF_6'))),B_2464)
      | ~ r1_tarski('#skF_6',B_2464)
      | ~ r1_tarski(k5_relat_1('#skF_7',k6_relat_1('#skF_6')),'#skF_7')
      | ~ v1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_13085])).

tff(c_13092,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_13086])).

tff(c_13095,plain,
    ( ~ v1_relat_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_13092])).

tff(c_13099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22,c_13095])).

tff(c_13101,plain,(
    v1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_13086])).

tff(c_1436,plain,(
    ! [D_325,C_326,B_327] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_325,k6_relat_1(C_326)),B_327),'#skF_5'(k5_relat_1(D_325,k6_relat_1(C_326)),B_327)),D_325)
      | ~ v1_relat_1(D_325)
      | r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_325,k6_relat_1(C_326)),B_327),'#skF_3'(k5_relat_1(D_325,k6_relat_1(C_326)),B_327)),B_327)
      | k5_relat_1(D_325,k6_relat_1(C_326)) = B_327
      | ~ v1_relat_1(B_327)
      | ~ v1_relat_1(k5_relat_1(D_325,k6_relat_1(C_326))) ) ),
    inference(resolution,[status(thm)],[c_143,c_30])).

tff(c_10316,plain,(
    ! [D_1985,C_1986,B_1987] :
      ( r2_hidden('#skF_3'(k5_relat_1(D_1985,k6_relat_1(C_1986)),B_1987),k2_relat_1(B_1987))
      | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_1985,k6_relat_1(C_1986)),B_1987),'#skF_5'(k5_relat_1(D_1985,k6_relat_1(C_1986)),B_1987)),D_1985)
      | ~ v1_relat_1(D_1985)
      | k5_relat_1(D_1985,k6_relat_1(C_1986)) = B_1987
      | ~ v1_relat_1(B_1987)
      | ~ v1_relat_1(k5_relat_1(D_1985,k6_relat_1(C_1986))) ) ),
    inference(resolution,[status(thm)],[c_1436,c_24])).

tff(c_416,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_3'(A_116,B_117),k2_relat_1(B_117))
      | ~ r2_hidden(k4_tarski('#skF_4'(A_116,B_117),'#skF_5'(A_116,B_117)),B_117)
      | B_117 = A_116
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_380,c_24])).

tff(c_10389,plain,(
    ! [D_1988,C_1989] :
      ( r2_hidden('#skF_3'(k5_relat_1(D_1988,k6_relat_1(C_1989)),D_1988),k2_relat_1(D_1988))
      | k5_relat_1(D_1988,k6_relat_1(C_1989)) = D_1988
      | ~ v1_relat_1(D_1988)
      | ~ v1_relat_1(k5_relat_1(D_1988,k6_relat_1(C_1989))) ) ),
    inference(resolution,[status(thm)],[c_10316,c_416])).

tff(c_10396,plain,(
    ! [D_1990,C_1991,B_1992] :
      ( r2_hidden('#skF_3'(k5_relat_1(D_1990,k6_relat_1(C_1991)),D_1990),B_1992)
      | ~ r1_tarski(k2_relat_1(D_1990),B_1992)
      | k5_relat_1(D_1990,k6_relat_1(C_1991)) = D_1990
      | ~ v1_relat_1(D_1990)
      | ~ v1_relat_1(k5_relat_1(D_1990,k6_relat_1(C_1991))) ) ),
    inference(resolution,[status(thm)],[c_10389,c_2])).

tff(c_10403,plain,(
    ! [D_1993,C_1994,B_1995,B_1996] :
      ( r2_hidden('#skF_3'(k5_relat_1(D_1993,k6_relat_1(C_1994)),D_1993),B_1995)
      | ~ r1_tarski(B_1996,B_1995)
      | ~ r1_tarski(k2_relat_1(D_1993),B_1996)
      | k5_relat_1(D_1993,k6_relat_1(C_1994)) = D_1993
      | ~ v1_relat_1(D_1993)
      | ~ v1_relat_1(k5_relat_1(D_1993,k6_relat_1(C_1994))) ) ),
    inference(resolution,[status(thm)],[c_10396,c_2])).

tff(c_10409,plain,(
    ! [D_1993,C_1994] :
      ( r2_hidden('#skF_3'(k5_relat_1(D_1993,k6_relat_1(C_1994)),D_1993),'#skF_6')
      | ~ r1_tarski(k2_relat_1(D_1993),k2_relat_1('#skF_7'))
      | k5_relat_1(D_1993,k6_relat_1(C_1994)) = D_1993
      | ~ v1_relat_1(D_1993)
      | ~ v1_relat_1(k5_relat_1(D_1993,k6_relat_1(C_1994))) ) ),
    inference(resolution,[status(thm)],[c_36,c_10403])).

tff(c_193,plain,(
    ! [D_32,C_31,B_95] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_32,k6_relat_1(C_31)),B_95),'#skF_5'(k5_relat_1(D_32,k6_relat_1(C_31)),B_95)),D_32)
      | ~ v1_relat_1(D_32)
      | r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_32,k6_relat_1(C_31)),B_95),'#skF_3'(k5_relat_1(D_32,k6_relat_1(C_31)),B_95)),B_95)
      | k5_relat_1(D_32,k6_relat_1(C_31)) = B_95
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k5_relat_1(D_32,k6_relat_1(C_31))) ) ),
    inference(resolution,[status(thm)],[c_143,c_30])).

tff(c_198,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_96,B_97),'#skF_3'(A_96,B_97)),A_96)
      | r2_hidden(k4_tarski('#skF_4'(A_96,B_97),'#skF_5'(A_96,B_97)),A_96)
      | B_97 = A_96
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1844,plain,(
    ! [D_394,C_395,B_396] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_394,k6_relat_1(C_395)),B_396),'#skF_5'(k5_relat_1(D_394,k6_relat_1(C_395)),B_396)),k5_relat_1(D_394,k6_relat_1(C_395)))
      | k5_relat_1(D_394,k6_relat_1(C_395)) = B_396
      | ~ v1_relat_1(B_396)
      | ~ v1_relat_1(k5_relat_1(D_394,k6_relat_1(C_395)))
      | ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_394,k6_relat_1(C_395)),B_396),'#skF_3'(k5_relat_1(D_394,k6_relat_1(C_395)),B_396)),D_394)
      | ~ r2_hidden('#skF_3'(k5_relat_1(D_394,k6_relat_1(C_395)),B_396),C_395)
      | ~ v1_relat_1(D_394) ) ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_17522,plain,(
    ! [D_2820,C_2821,B_2822] :
      ( r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_2820,k6_relat_1(C_2821)),B_2822),'#skF_5'(k5_relat_1(D_2820,k6_relat_1(C_2821)),B_2822)),D_2820)
      | k5_relat_1(D_2820,k6_relat_1(C_2821)) = B_2822
      | ~ v1_relat_1(B_2822)
      | ~ v1_relat_1(k5_relat_1(D_2820,k6_relat_1(C_2821)))
      | ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_2820,k6_relat_1(C_2821)),B_2822),'#skF_3'(k5_relat_1(D_2820,k6_relat_1(C_2821)),B_2822)),D_2820)
      | ~ r2_hidden('#skF_3'(k5_relat_1(D_2820,k6_relat_1(C_2821)),B_2822),C_2821)
      | ~ v1_relat_1(D_2820) ) ),
    inference(resolution,[status(thm)],[c_1844,c_30])).

tff(c_17816,plain,(
    ! [B_95,C_31] :
      ( ~ r2_hidden('#skF_3'(k5_relat_1(B_95,k6_relat_1(C_31)),B_95),C_31)
      | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(B_95,k6_relat_1(C_31)),B_95),'#skF_5'(k5_relat_1(B_95,k6_relat_1(C_31)),B_95)),B_95)
      | k5_relat_1(B_95,k6_relat_1(C_31)) = B_95
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k5_relat_1(B_95,k6_relat_1(C_31))) ) ),
    inference(resolution,[status(thm)],[c_193,c_17522])).

tff(c_10,plain,(
    ! [A_6,B_16] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6,B_16),'#skF_3'(A_6,B_16)),B_16)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_6,B_16),'#skF_5'(A_6,B_16)),B_16)
      | B_16 = A_6
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18219,plain,(
    ! [B_2894,C_2895] :
      ( ~ r2_hidden('#skF_3'(k5_relat_1(B_2894,k6_relat_1(C_2895)),B_2894),C_2895)
      | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(B_2894,k6_relat_1(C_2895)),B_2894),'#skF_5'(k5_relat_1(B_2894,k6_relat_1(C_2895)),B_2894)),B_2894)
      | k5_relat_1(B_2894,k6_relat_1(C_2895)) = B_2894
      | ~ v1_relat_1(B_2894)
      | ~ v1_relat_1(k5_relat_1(B_2894,k6_relat_1(C_2895))) ) ),
    inference(resolution,[status(thm)],[c_193,c_17522])).

tff(c_252,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_104,B_105),'#skF_3'(A_104,B_105)),A_104)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_104,B_105),'#skF_5'(A_104,B_105)),B_105)
      | B_105 = A_104
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_261,plain,(
    ! [D_32,C_31,B_105] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_32,k6_relat_1(C_31)),B_105),'#skF_5'(k5_relat_1(D_32,k6_relat_1(C_31)),B_105)),B_105)
      | k5_relat_1(D_32,k6_relat_1(C_31)) = B_105
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(k5_relat_1(D_32,k6_relat_1(C_31)))
      | ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_32,k6_relat_1(C_31)),B_105),'#skF_3'(k5_relat_1(D_32,k6_relat_1(C_31)),B_105)),D_32)
      | ~ r2_hidden('#skF_3'(k5_relat_1(D_32,k6_relat_1(C_31)),B_105),C_31)
      | ~ v1_relat_1(D_32) ) ),
    inference(resolution,[status(thm)],[c_28,c_252])).

tff(c_21184,plain,(
    ! [B_3164,C_3165] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(k5_relat_1(B_3164,k6_relat_1(C_3165)),B_3164),'#skF_3'(k5_relat_1(B_3164,k6_relat_1(C_3165)),B_3164)),B_3164)
      | ~ r2_hidden('#skF_3'(k5_relat_1(B_3164,k6_relat_1(C_3165)),B_3164),C_3165)
      | k5_relat_1(B_3164,k6_relat_1(C_3165)) = B_3164
      | ~ v1_relat_1(B_3164)
      | ~ v1_relat_1(k5_relat_1(B_3164,k6_relat_1(C_3165))) ) ),
    inference(resolution,[status(thm)],[c_18219,c_261])).

tff(c_26236,plain,(
    ! [B_3351,C_3352] :
      ( ~ r2_hidden('#skF_3'(k5_relat_1(B_3351,k6_relat_1(C_3352)),B_3351),C_3352)
      | ~ r2_hidden(k4_tarski('#skF_4'(k5_relat_1(B_3351,k6_relat_1(C_3352)),B_3351),'#skF_5'(k5_relat_1(B_3351,k6_relat_1(C_3352)),B_3351)),B_3351)
      | k5_relat_1(B_3351,k6_relat_1(C_3352)) = B_3351
      | ~ v1_relat_1(B_3351)
      | ~ v1_relat_1(k5_relat_1(B_3351,k6_relat_1(C_3352))) ) ),
    inference(resolution,[status(thm)],[c_10,c_21184])).

tff(c_26482,plain,(
    ! [B_3353,C_3354] :
      ( ~ r2_hidden('#skF_3'(k5_relat_1(B_3353,k6_relat_1(C_3354)),B_3353),C_3354)
      | k5_relat_1(B_3353,k6_relat_1(C_3354)) = B_3353
      | ~ v1_relat_1(B_3353)
      | ~ v1_relat_1(k5_relat_1(B_3353,k6_relat_1(C_3354))) ) ),
    inference(resolution,[status(thm)],[c_17816,c_26236])).

tff(c_27024,plain,(
    ! [D_3356] :
      ( ~ r1_tarski(k2_relat_1(D_3356),k2_relat_1('#skF_7'))
      | k5_relat_1(D_3356,k6_relat_1('#skF_6')) = D_3356
      | ~ v1_relat_1(D_3356)
      | ~ v1_relat_1(k5_relat_1(D_3356,k6_relat_1('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_10409,c_26482])).

tff(c_27028,plain,
    ( k5_relat_1('#skF_7',k6_relat_1('#skF_6')) = '#skF_7'
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_47,c_27024])).

tff(c_27031,plain,(
    k5_relat_1('#skF_7',k6_relat_1('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13101,c_38,c_27028])).

tff(c_27033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_27031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.27/20.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.27/20.82  
% 30.27/20.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.27/20.83  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 30.27/20.83  
% 30.27/20.83  %Foreground sorts:
% 30.27/20.83  
% 30.27/20.83  
% 30.27/20.83  %Background operators:
% 30.27/20.83  
% 30.27/20.83  
% 30.27/20.83  %Foreground operators:
% 30.27/20.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.27/20.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.27/20.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 30.27/20.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 30.27/20.83  tff('#skF_7', type, '#skF_7': $i).
% 30.27/20.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 30.27/20.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.27/20.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.27/20.83  tff('#skF_6', type, '#skF_6': $i).
% 30.27/20.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.27/20.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.27/20.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 30.27/20.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.27/20.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 30.27/20.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 30.27/20.83  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 30.27/20.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.27/20.83  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 30.27/20.83  
% 30.43/20.84  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 30.43/20.84  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 30.43/20.84  tff(f_50, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 30.43/20.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 30.43/20.84  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_relat_1)).
% 30.43/20.84  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 30.43/20.84  tff(f_68, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_relat_1)).
% 30.43/20.84  tff(c_34, plain, (k5_relat_1('#skF_7', k6_relat_1('#skF_6'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_75])).
% 30.43/20.84  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 30.43/20.84  tff(c_22, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.43/20.84  tff(c_20, plain, (![A_23, B_24]: (v1_relat_1(k5_relat_1(A_23, B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 30.43/20.84  tff(c_42, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.43/20.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.43/20.84  tff(c_47, plain, (![A_38]: (r1_tarski(A_38, A_38))), inference(resolution, [status(thm)], [c_42, c_4])).
% 30.43/20.84  tff(c_36, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 30.43/20.84  tff(c_143, plain, (![A_94, B_95]: (r2_hidden(k4_tarski('#skF_2'(A_94, B_95), '#skF_3'(A_94, B_95)), B_95) | r2_hidden(k4_tarski('#skF_4'(A_94, B_95), '#skF_5'(A_94, B_95)), A_94) | B_95=A_94 | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_44])).
% 30.43/20.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 30.43/20.84  tff(c_652, plain, (![A_166, B_167, B_168]: (r2_hidden(k4_tarski('#skF_2'(A_166, B_167), '#skF_3'(A_166, B_167)), B_168) | ~r1_tarski(B_167, B_168) | r2_hidden(k4_tarski('#skF_4'(A_166, B_167), '#skF_5'(A_166, B_167)), A_166) | B_167=A_166 | ~v1_relat_1(B_167) | ~v1_relat_1(A_166))), inference(resolution, [status(thm)], [c_143, c_2])).
% 30.43/20.84  tff(c_12, plain, (![A_6, B_16]: (~r2_hidden(k4_tarski('#skF_2'(A_6, B_16), '#skF_3'(A_6, B_16)), A_6) | r2_hidden(k4_tarski('#skF_4'(A_6, B_16), '#skF_5'(A_6, B_16)), A_6) | B_16=A_6 | ~v1_relat_1(B_16) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 30.43/20.84  tff(c_728, plain, (![B_169, B_170]: (~r1_tarski(B_169, B_170) | r2_hidden(k4_tarski('#skF_4'(B_170, B_169), '#skF_5'(B_170, B_169)), B_170) | B_170=B_169 | ~v1_relat_1(B_169) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_652, c_12])).
% 30.43/20.84  tff(c_24, plain, (![B_27, C_28, A_26]: (r2_hidden(B_27, k2_relat_1(C_28)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 30.43/20.84  tff(c_772, plain, (![B_171, B_172]: (r2_hidden('#skF_5'(B_171, B_172), k2_relat_1(B_171)) | ~r1_tarski(B_172, B_171) | B_172=B_171 | ~v1_relat_1(B_172) | ~v1_relat_1(B_171))), inference(resolution, [status(thm)], [c_728, c_24])).
% 30.43/20.84  tff(c_787, plain, (![B_178, B_179, B_180]: (r2_hidden('#skF_5'(B_178, B_179), B_180) | ~r1_tarski(k2_relat_1(B_178), B_180) | ~r1_tarski(B_179, B_178) | B_179=B_178 | ~v1_relat_1(B_179) | ~v1_relat_1(B_178))), inference(resolution, [status(thm)], [c_772, c_2])).
% 30.43/20.84  tff(c_894, plain, (![B_207, B_208, B_209, B_210]: (r2_hidden('#skF_5'(B_207, B_208), B_209) | ~r1_tarski(B_210, B_209) | ~r1_tarski(k2_relat_1(B_207), B_210) | ~r1_tarski(B_208, B_207) | B_208=B_207 | ~v1_relat_1(B_208) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_787, c_2])).
% 30.43/20.84  tff(c_901, plain, (![B_211, B_212]: (r2_hidden('#skF_5'(B_211, B_212), '#skF_6') | ~r1_tarski(k2_relat_1(B_211), k2_relat_1('#skF_7')) | ~r1_tarski(B_212, B_211) | B_212=B_211 | ~v1_relat_1(B_212) | ~v1_relat_1(B_211))), inference(resolution, [status(thm)], [c_36, c_894])).
% 30.43/20.84  tff(c_904, plain, (![B_212]: (r2_hidden('#skF_5'('#skF_7', B_212), '#skF_6') | ~r1_tarski(B_212, '#skF_7') | B_212='#skF_7' | ~v1_relat_1(B_212) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_47, c_901])).
% 30.43/20.84  tff(c_907, plain, (![B_212]: (r2_hidden('#skF_5'('#skF_7', B_212), '#skF_6') | ~r1_tarski(B_212, '#skF_7') | B_212='#skF_7' | ~v1_relat_1(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_904])).
% 30.43/20.84  tff(c_30, plain, (![A_29, B_30, D_32, C_31]: (r2_hidden(k4_tarski(A_29, B_30), D_32) | ~r2_hidden(k4_tarski(A_29, B_30), k5_relat_1(D_32, k6_relat_1(C_31))) | ~v1_relat_1(D_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 30.43/20.84  tff(c_1300, plain, (![A_301, D_302, C_303]: (r2_hidden(k4_tarski('#skF_2'(A_301, k5_relat_1(D_302, k6_relat_1(C_303))), '#skF_3'(A_301, k5_relat_1(D_302, k6_relat_1(C_303)))), D_302) | ~v1_relat_1(D_302) | r2_hidden(k4_tarski('#skF_4'(A_301, k5_relat_1(D_302, k6_relat_1(C_303))), '#skF_5'(A_301, k5_relat_1(D_302, k6_relat_1(C_303)))), A_301) | k5_relat_1(D_302, k6_relat_1(C_303))=A_301 | ~v1_relat_1(k5_relat_1(D_302, k6_relat_1(C_303))) | ~v1_relat_1(A_301))), inference(resolution, [status(thm)], [c_143, c_30])).
% 30.43/20.84  tff(c_1364, plain, (![D_302, C_303]: (r2_hidden(k4_tarski('#skF_4'(D_302, k5_relat_1(D_302, k6_relat_1(C_303))), '#skF_5'(D_302, k5_relat_1(D_302, k6_relat_1(C_303)))), D_302) | k5_relat_1(D_302, k6_relat_1(C_303))=D_302 | ~v1_relat_1(k5_relat_1(D_302, k6_relat_1(C_303))) | ~v1_relat_1(D_302))), inference(resolution, [status(thm)], [c_1300, c_12])).
% 30.43/20.84  tff(c_28, plain, (![A_29, B_30, D_32, C_31]: (r2_hidden(k4_tarski(A_29, B_30), k5_relat_1(D_32, k6_relat_1(C_31))) | ~r2_hidden(k4_tarski(A_29, B_30), D_32) | ~r2_hidden(B_30, C_31) | ~v1_relat_1(D_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 30.43/20.84  tff(c_380, plain, (![A_116, B_117]: (r2_hidden(k4_tarski('#skF_2'(A_116, B_117), '#skF_3'(A_116, B_117)), B_117) | ~r2_hidden(k4_tarski('#skF_4'(A_116, B_117), '#skF_5'(A_116, B_117)), B_117) | B_117=A_116 | ~v1_relat_1(B_117) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_44])).
% 30.43/20.84  tff(c_32, plain, (![B_30, C_31, A_29, D_32]: (r2_hidden(B_30, C_31) | ~r2_hidden(k4_tarski(A_29, B_30), k5_relat_1(D_32, k6_relat_1(C_31))) | ~v1_relat_1(D_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 30.43/20.84  tff(c_1207, plain, (![A_278, D_279, C_280]: (r2_hidden('#skF_3'(A_278, k5_relat_1(D_279, k6_relat_1(C_280))), C_280) | ~v1_relat_1(D_279) | ~r2_hidden(k4_tarski('#skF_4'(A_278, k5_relat_1(D_279, k6_relat_1(C_280))), '#skF_5'(A_278, k5_relat_1(D_279, k6_relat_1(C_280)))), k5_relat_1(D_279, k6_relat_1(C_280))) | k5_relat_1(D_279, k6_relat_1(C_280))=A_278 | ~v1_relat_1(k5_relat_1(D_279, k6_relat_1(C_280))) | ~v1_relat_1(A_278))), inference(resolution, [status(thm)], [c_380, c_32])).
% 30.43/20.84  tff(c_12458, plain, (![A_2453, D_2454, C_2455]: (r2_hidden('#skF_3'(A_2453, k5_relat_1(D_2454, k6_relat_1(C_2455))), C_2455) | k5_relat_1(D_2454, k6_relat_1(C_2455))=A_2453 | ~v1_relat_1(k5_relat_1(D_2454, k6_relat_1(C_2455))) | ~v1_relat_1(A_2453) | ~r2_hidden(k4_tarski('#skF_4'(A_2453, k5_relat_1(D_2454, k6_relat_1(C_2455))), '#skF_5'(A_2453, k5_relat_1(D_2454, k6_relat_1(C_2455)))), D_2454) | ~r2_hidden('#skF_5'(A_2453, k5_relat_1(D_2454, k6_relat_1(C_2455))), C_2455) | ~v1_relat_1(D_2454))), inference(resolution, [status(thm)], [c_28, c_1207])).
% 30.43/20.84  tff(c_12768, plain, (![D_2456, C_2457]: (r2_hidden('#skF_3'(D_2456, k5_relat_1(D_2456, k6_relat_1(C_2457))), C_2457) | ~r2_hidden('#skF_5'(D_2456, k5_relat_1(D_2456, k6_relat_1(C_2457))), C_2457) | k5_relat_1(D_2456, k6_relat_1(C_2457))=D_2456 | ~v1_relat_1(k5_relat_1(D_2456, k6_relat_1(C_2457))) | ~v1_relat_1(D_2456))), inference(resolution, [status(thm)], [c_1364, c_12458])).
% 30.43/20.84  tff(c_12780, plain, (![D_2462, C_2463, B_2464]: (r2_hidden('#skF_3'(D_2462, k5_relat_1(D_2462, k6_relat_1(C_2463))), B_2464) | ~r1_tarski(C_2463, B_2464) | ~r2_hidden('#skF_5'(D_2462, k5_relat_1(D_2462, k6_relat_1(C_2463))), C_2463) | k5_relat_1(D_2462, k6_relat_1(C_2463))=D_2462 | ~v1_relat_1(k5_relat_1(D_2462, k6_relat_1(C_2463))) | ~v1_relat_1(D_2462))), inference(resolution, [status(thm)], [c_12768, c_2])).
% 30.43/20.84  tff(c_12999, plain, (![B_2464]: (r2_hidden('#skF_3'('#skF_7', k5_relat_1('#skF_7', k6_relat_1('#skF_6'))), B_2464) | ~r1_tarski('#skF_6', B_2464) | ~v1_relat_1('#skF_7') | ~r1_tarski(k5_relat_1('#skF_7', k6_relat_1('#skF_6')), '#skF_7') | k5_relat_1('#skF_7', k6_relat_1('#skF_6'))='#skF_7' | ~v1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6'))))), inference(resolution, [status(thm)], [c_907, c_12780])).
% 30.43/20.84  tff(c_13085, plain, (![B_2464]: (r2_hidden('#skF_3'('#skF_7', k5_relat_1('#skF_7', k6_relat_1('#skF_6'))), B_2464) | ~r1_tarski('#skF_6', B_2464) | ~r1_tarski(k5_relat_1('#skF_7', k6_relat_1('#skF_6')), '#skF_7') | k5_relat_1('#skF_7', k6_relat_1('#skF_6'))='#skF_7' | ~v1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12999])).
% 30.43/20.84  tff(c_13086, plain, (![B_2464]: (r2_hidden('#skF_3'('#skF_7', k5_relat_1('#skF_7', k6_relat_1('#skF_6'))), B_2464) | ~r1_tarski('#skF_6', B_2464) | ~r1_tarski(k5_relat_1('#skF_7', k6_relat_1('#skF_6')), '#skF_7') | ~v1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_13085])).
% 30.43/20.84  tff(c_13092, plain, (~v1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_13086])).
% 30.43/20.84  tff(c_13095, plain, (~v1_relat_1(k6_relat_1('#skF_6')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_13092])).
% 30.43/20.84  tff(c_13099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_22, c_13095])).
% 30.43/20.84  tff(c_13101, plain, (v1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_13086])).
% 30.43/20.84  tff(c_1436, plain, (![D_325, C_326, B_327]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_325, k6_relat_1(C_326)), B_327), '#skF_5'(k5_relat_1(D_325, k6_relat_1(C_326)), B_327)), D_325) | ~v1_relat_1(D_325) | r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_325, k6_relat_1(C_326)), B_327), '#skF_3'(k5_relat_1(D_325, k6_relat_1(C_326)), B_327)), B_327) | k5_relat_1(D_325, k6_relat_1(C_326))=B_327 | ~v1_relat_1(B_327) | ~v1_relat_1(k5_relat_1(D_325, k6_relat_1(C_326))))), inference(resolution, [status(thm)], [c_143, c_30])).
% 30.43/20.84  tff(c_10316, plain, (![D_1985, C_1986, B_1987]: (r2_hidden('#skF_3'(k5_relat_1(D_1985, k6_relat_1(C_1986)), B_1987), k2_relat_1(B_1987)) | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_1985, k6_relat_1(C_1986)), B_1987), '#skF_5'(k5_relat_1(D_1985, k6_relat_1(C_1986)), B_1987)), D_1985) | ~v1_relat_1(D_1985) | k5_relat_1(D_1985, k6_relat_1(C_1986))=B_1987 | ~v1_relat_1(B_1987) | ~v1_relat_1(k5_relat_1(D_1985, k6_relat_1(C_1986))))), inference(resolution, [status(thm)], [c_1436, c_24])).
% 30.43/20.84  tff(c_416, plain, (![A_116, B_117]: (r2_hidden('#skF_3'(A_116, B_117), k2_relat_1(B_117)) | ~r2_hidden(k4_tarski('#skF_4'(A_116, B_117), '#skF_5'(A_116, B_117)), B_117) | B_117=A_116 | ~v1_relat_1(B_117) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_380, c_24])).
% 30.43/20.84  tff(c_10389, plain, (![D_1988, C_1989]: (r2_hidden('#skF_3'(k5_relat_1(D_1988, k6_relat_1(C_1989)), D_1988), k2_relat_1(D_1988)) | k5_relat_1(D_1988, k6_relat_1(C_1989))=D_1988 | ~v1_relat_1(D_1988) | ~v1_relat_1(k5_relat_1(D_1988, k6_relat_1(C_1989))))), inference(resolution, [status(thm)], [c_10316, c_416])).
% 30.43/20.84  tff(c_10396, plain, (![D_1990, C_1991, B_1992]: (r2_hidden('#skF_3'(k5_relat_1(D_1990, k6_relat_1(C_1991)), D_1990), B_1992) | ~r1_tarski(k2_relat_1(D_1990), B_1992) | k5_relat_1(D_1990, k6_relat_1(C_1991))=D_1990 | ~v1_relat_1(D_1990) | ~v1_relat_1(k5_relat_1(D_1990, k6_relat_1(C_1991))))), inference(resolution, [status(thm)], [c_10389, c_2])).
% 30.43/20.84  tff(c_10403, plain, (![D_1993, C_1994, B_1995, B_1996]: (r2_hidden('#skF_3'(k5_relat_1(D_1993, k6_relat_1(C_1994)), D_1993), B_1995) | ~r1_tarski(B_1996, B_1995) | ~r1_tarski(k2_relat_1(D_1993), B_1996) | k5_relat_1(D_1993, k6_relat_1(C_1994))=D_1993 | ~v1_relat_1(D_1993) | ~v1_relat_1(k5_relat_1(D_1993, k6_relat_1(C_1994))))), inference(resolution, [status(thm)], [c_10396, c_2])).
% 30.43/20.84  tff(c_10409, plain, (![D_1993, C_1994]: (r2_hidden('#skF_3'(k5_relat_1(D_1993, k6_relat_1(C_1994)), D_1993), '#skF_6') | ~r1_tarski(k2_relat_1(D_1993), k2_relat_1('#skF_7')) | k5_relat_1(D_1993, k6_relat_1(C_1994))=D_1993 | ~v1_relat_1(D_1993) | ~v1_relat_1(k5_relat_1(D_1993, k6_relat_1(C_1994))))), inference(resolution, [status(thm)], [c_36, c_10403])).
% 30.43/20.84  tff(c_193, plain, (![D_32, C_31, B_95]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_32, k6_relat_1(C_31)), B_95), '#skF_5'(k5_relat_1(D_32, k6_relat_1(C_31)), B_95)), D_32) | ~v1_relat_1(D_32) | r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_32, k6_relat_1(C_31)), B_95), '#skF_3'(k5_relat_1(D_32, k6_relat_1(C_31)), B_95)), B_95) | k5_relat_1(D_32, k6_relat_1(C_31))=B_95 | ~v1_relat_1(B_95) | ~v1_relat_1(k5_relat_1(D_32, k6_relat_1(C_31))))), inference(resolution, [status(thm)], [c_143, c_30])).
% 30.43/20.84  tff(c_198, plain, (![A_96, B_97]: (~r2_hidden(k4_tarski('#skF_2'(A_96, B_97), '#skF_3'(A_96, B_97)), A_96) | r2_hidden(k4_tarski('#skF_4'(A_96, B_97), '#skF_5'(A_96, B_97)), A_96) | B_97=A_96 | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_44])).
% 30.43/20.84  tff(c_1844, plain, (![D_394, C_395, B_396]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_394, k6_relat_1(C_395)), B_396), '#skF_5'(k5_relat_1(D_394, k6_relat_1(C_395)), B_396)), k5_relat_1(D_394, k6_relat_1(C_395))) | k5_relat_1(D_394, k6_relat_1(C_395))=B_396 | ~v1_relat_1(B_396) | ~v1_relat_1(k5_relat_1(D_394, k6_relat_1(C_395))) | ~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_394, k6_relat_1(C_395)), B_396), '#skF_3'(k5_relat_1(D_394, k6_relat_1(C_395)), B_396)), D_394) | ~r2_hidden('#skF_3'(k5_relat_1(D_394, k6_relat_1(C_395)), B_396), C_395) | ~v1_relat_1(D_394))), inference(resolution, [status(thm)], [c_28, c_198])).
% 30.43/20.84  tff(c_17522, plain, (![D_2820, C_2821, B_2822]: (r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_2820, k6_relat_1(C_2821)), B_2822), '#skF_5'(k5_relat_1(D_2820, k6_relat_1(C_2821)), B_2822)), D_2820) | k5_relat_1(D_2820, k6_relat_1(C_2821))=B_2822 | ~v1_relat_1(B_2822) | ~v1_relat_1(k5_relat_1(D_2820, k6_relat_1(C_2821))) | ~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_2820, k6_relat_1(C_2821)), B_2822), '#skF_3'(k5_relat_1(D_2820, k6_relat_1(C_2821)), B_2822)), D_2820) | ~r2_hidden('#skF_3'(k5_relat_1(D_2820, k6_relat_1(C_2821)), B_2822), C_2821) | ~v1_relat_1(D_2820))), inference(resolution, [status(thm)], [c_1844, c_30])).
% 30.43/20.84  tff(c_17816, plain, (![B_95, C_31]: (~r2_hidden('#skF_3'(k5_relat_1(B_95, k6_relat_1(C_31)), B_95), C_31) | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(B_95, k6_relat_1(C_31)), B_95), '#skF_5'(k5_relat_1(B_95, k6_relat_1(C_31)), B_95)), B_95) | k5_relat_1(B_95, k6_relat_1(C_31))=B_95 | ~v1_relat_1(B_95) | ~v1_relat_1(k5_relat_1(B_95, k6_relat_1(C_31))))), inference(resolution, [status(thm)], [c_193, c_17522])).
% 30.43/20.84  tff(c_10, plain, (![A_6, B_16]: (r2_hidden(k4_tarski('#skF_2'(A_6, B_16), '#skF_3'(A_6, B_16)), B_16) | ~r2_hidden(k4_tarski('#skF_4'(A_6, B_16), '#skF_5'(A_6, B_16)), B_16) | B_16=A_6 | ~v1_relat_1(B_16) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 30.43/20.84  tff(c_18219, plain, (![B_2894, C_2895]: (~r2_hidden('#skF_3'(k5_relat_1(B_2894, k6_relat_1(C_2895)), B_2894), C_2895) | r2_hidden(k4_tarski('#skF_4'(k5_relat_1(B_2894, k6_relat_1(C_2895)), B_2894), '#skF_5'(k5_relat_1(B_2894, k6_relat_1(C_2895)), B_2894)), B_2894) | k5_relat_1(B_2894, k6_relat_1(C_2895))=B_2894 | ~v1_relat_1(B_2894) | ~v1_relat_1(k5_relat_1(B_2894, k6_relat_1(C_2895))))), inference(resolution, [status(thm)], [c_193, c_17522])).
% 30.43/20.84  tff(c_252, plain, (![A_104, B_105]: (~r2_hidden(k4_tarski('#skF_2'(A_104, B_105), '#skF_3'(A_104, B_105)), A_104) | ~r2_hidden(k4_tarski('#skF_4'(A_104, B_105), '#skF_5'(A_104, B_105)), B_105) | B_105=A_104 | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_44])).
% 30.43/20.84  tff(c_261, plain, (![D_32, C_31, B_105]: (~r2_hidden(k4_tarski('#skF_4'(k5_relat_1(D_32, k6_relat_1(C_31)), B_105), '#skF_5'(k5_relat_1(D_32, k6_relat_1(C_31)), B_105)), B_105) | k5_relat_1(D_32, k6_relat_1(C_31))=B_105 | ~v1_relat_1(B_105) | ~v1_relat_1(k5_relat_1(D_32, k6_relat_1(C_31))) | ~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(D_32, k6_relat_1(C_31)), B_105), '#skF_3'(k5_relat_1(D_32, k6_relat_1(C_31)), B_105)), D_32) | ~r2_hidden('#skF_3'(k5_relat_1(D_32, k6_relat_1(C_31)), B_105), C_31) | ~v1_relat_1(D_32))), inference(resolution, [status(thm)], [c_28, c_252])).
% 30.43/20.84  tff(c_21184, plain, (![B_3164, C_3165]: (~r2_hidden(k4_tarski('#skF_2'(k5_relat_1(B_3164, k6_relat_1(C_3165)), B_3164), '#skF_3'(k5_relat_1(B_3164, k6_relat_1(C_3165)), B_3164)), B_3164) | ~r2_hidden('#skF_3'(k5_relat_1(B_3164, k6_relat_1(C_3165)), B_3164), C_3165) | k5_relat_1(B_3164, k6_relat_1(C_3165))=B_3164 | ~v1_relat_1(B_3164) | ~v1_relat_1(k5_relat_1(B_3164, k6_relat_1(C_3165))))), inference(resolution, [status(thm)], [c_18219, c_261])).
% 30.43/20.84  tff(c_26236, plain, (![B_3351, C_3352]: (~r2_hidden('#skF_3'(k5_relat_1(B_3351, k6_relat_1(C_3352)), B_3351), C_3352) | ~r2_hidden(k4_tarski('#skF_4'(k5_relat_1(B_3351, k6_relat_1(C_3352)), B_3351), '#skF_5'(k5_relat_1(B_3351, k6_relat_1(C_3352)), B_3351)), B_3351) | k5_relat_1(B_3351, k6_relat_1(C_3352))=B_3351 | ~v1_relat_1(B_3351) | ~v1_relat_1(k5_relat_1(B_3351, k6_relat_1(C_3352))))), inference(resolution, [status(thm)], [c_10, c_21184])).
% 30.43/20.84  tff(c_26482, plain, (![B_3353, C_3354]: (~r2_hidden('#skF_3'(k5_relat_1(B_3353, k6_relat_1(C_3354)), B_3353), C_3354) | k5_relat_1(B_3353, k6_relat_1(C_3354))=B_3353 | ~v1_relat_1(B_3353) | ~v1_relat_1(k5_relat_1(B_3353, k6_relat_1(C_3354))))), inference(resolution, [status(thm)], [c_17816, c_26236])).
% 30.43/20.84  tff(c_27024, plain, (![D_3356]: (~r1_tarski(k2_relat_1(D_3356), k2_relat_1('#skF_7')) | k5_relat_1(D_3356, k6_relat_1('#skF_6'))=D_3356 | ~v1_relat_1(D_3356) | ~v1_relat_1(k5_relat_1(D_3356, k6_relat_1('#skF_6'))))), inference(resolution, [status(thm)], [c_10409, c_26482])).
% 30.43/20.84  tff(c_27028, plain, (k5_relat_1('#skF_7', k6_relat_1('#skF_6'))='#skF_7' | ~v1_relat_1('#skF_7') | ~v1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_47, c_27024])).
% 30.43/20.84  tff(c_27031, plain, (k5_relat_1('#skF_7', k6_relat_1('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13101, c_38, c_27028])).
% 30.43/20.84  tff(c_27033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_27031])).
% 30.43/20.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.43/20.84  
% 30.43/20.84  Inference rules
% 30.43/20.84  ----------------------
% 30.43/20.84  #Ref     : 0
% 30.43/20.84  #Sup     : 6322
% 30.43/20.84  #Fact    : 6
% 30.43/20.84  #Define  : 0
% 30.43/20.84  #Split   : 13
% 30.43/20.84  #Chain   : 0
% 30.43/20.84  #Close   : 0
% 30.43/20.84  
% 30.43/20.84  Ordering : KBO
% 30.43/20.84  
% 30.43/20.84  Simplification rules
% 30.43/20.84  ----------------------
% 30.43/20.84  #Subsume      : 1794
% 30.43/20.84  #Demod        : 244
% 30.43/20.84  #Tautology    : 280
% 30.43/20.85  #SimpNegUnit  : 28
% 30.43/20.85  #BackRed      : 0
% 30.43/20.85  
% 30.43/20.85  #Partial instantiations: 0
% 30.43/20.85  #Strategies tried      : 1
% 30.43/20.85  
% 30.43/20.85  Timing (in seconds)
% 30.43/20.85  ----------------------
% 30.43/20.85  Preprocessing        : 0.28
% 30.43/20.85  Parsing              : 0.16
% 30.43/20.85  CNF conversion       : 0.02
% 30.43/20.85  Main loop            : 19.80
% 30.43/20.85  Inferencing          : 4.81
% 30.43/20.85  Reduction            : 2.83
% 30.43/20.85  Demodulation         : 1.97
% 30.43/20.85  BG Simplification    : 0.18
% 30.43/20.85  Subsumption          : 11.30
% 30.43/20.85  Abstraction          : 0.31
% 30.43/20.85  MUC search           : 0.00
% 30.43/20.85  Cooper               : 0.00
% 30.43/20.85  Total                : 20.12
% 30.43/20.85  Index Insertion      : 0.00
% 30.43/20.85  Index Deletion       : 0.00
% 30.43/20.85  Index Matching       : 0.00
% 30.43/20.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
