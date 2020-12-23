%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 399 expanded)
%              Number of leaves         :   26 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 (1152 expanded)
%              Number of equality atoms :   36 ( 183 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( r2_hidden(B,A)
           => ( v3_ordinal1(B)
              & r1_tarski(B,A) ) )
       => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_63,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_ordinal1(A) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_31,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_106,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_110,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(c_66,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_1'(A_41),A_41)
      | v1_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [B_33] :
      ( v3_ordinal1(B_33)
      | ~ r2_hidden(B_33,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_71,plain,
    ( v3_ordinal1('#skF_1'('#skF_4'))
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_50])).

tff(c_78,plain,(
    v1_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_79,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_2'(A_43),A_43)
      | v2_ordinal1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_50])).

tff(c_90,plain,(
    v2_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_113,plain,(
    ! [A_46] :
      ( v3_ordinal1(A_46)
      | ~ v2_ordinal1(A_46)
      | ~ v1_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_122,plain,
    ( ~ v2_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_46])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_90,c_122])).

tff(c_130,plain,(
    ~ v2_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_26,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_140,plain,(
    ! [A_47] :
      ( '#skF_2'(A_47) != '#skF_3'(A_47)
      | v2_ordinal1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_144,plain,(
    '#skF_2'('#skF_4') != '#skF_3'('#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_130])).

tff(c_24,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_3'(A_8),A_8)
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_268,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | r2_hidden(A_68,B_67)
      | ~ r2_hidden(A_68,k1_ordinal1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4411,plain,(
    ! [B_263] :
      ( '#skF_3'(k1_ordinal1(B_263)) = B_263
      | r2_hidden('#skF_3'(k1_ordinal1(B_263)),B_263)
      | v2_ordinal1(k1_ordinal1(B_263)) ) ),
    inference(resolution,[status(thm)],[c_24,c_268])).

tff(c_4443,plain,
    ( v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4')))
    | '#skF_3'(k1_ordinal1('#skF_4')) = '#skF_4'
    | v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4411,c_50])).

tff(c_4444,plain,(
    v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4443])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(A_17,B_18)
      | r2_hidden(A_17,k1_ordinal1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_431,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | C_85 = B_86
      | r2_hidden(B_86,C_85)
      | ~ r2_hidden(C_85,A_87)
      | ~ r2_hidden(B_86,A_87)
      | ~ v2_ordinal1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5200,plain,(
    ! [A_322,B_323,B_324] :
      ( r2_hidden(A_322,B_323)
      | B_323 = A_322
      | r2_hidden(B_323,A_322)
      | ~ r2_hidden(B_323,k1_ordinal1(B_324))
      | ~ v2_ordinal1(k1_ordinal1(B_324))
      | ~ r2_hidden(A_322,B_324) ) ),
    inference(resolution,[status(thm)],[c_36,c_431])).

tff(c_5250,plain,(
    ! [A_325,A_326,B_327] :
      ( r2_hidden(A_325,A_326)
      | A_326 = A_325
      | r2_hidden(A_326,A_325)
      | ~ v2_ordinal1(k1_ordinal1(B_327))
      | ~ r2_hidden(A_325,B_327)
      | ~ r2_hidden(A_326,B_327) ) ),
    inference(resolution,[status(thm)],[c_36,c_5200])).

tff(c_5261,plain,(
    ! [A_328,A_329] :
      ( r2_hidden(A_328,A_329)
      | A_329 = A_328
      | r2_hidden(A_329,A_328)
      | ~ r2_hidden(A_328,'#skF_4')
      | ~ r2_hidden(A_329,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4444,c_5250])).

tff(c_5285,plain,(
    ! [A_329] :
      ( r2_hidden('#skF_3'('#skF_4'),A_329)
      | A_329 = '#skF_3'('#skF_4')
      | r2_hidden(A_329,'#skF_3'('#skF_4'))
      | ~ r2_hidden(A_329,'#skF_4')
      | v2_ordinal1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_5261])).

tff(c_5327,plain,(
    ! [A_330] :
      ( r2_hidden('#skF_3'('#skF_4'),A_330)
      | A_330 = '#skF_3'('#skF_4')
      | r2_hidden(A_330,'#skF_3'('#skF_4'))
      | ~ r2_hidden(A_330,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_5285])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2'(A_8),'#skF_3'(A_8))
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5368,plain,
    ( v2_ordinal1('#skF_4')
    | r2_hidden('#skF_3'('#skF_4'),'#skF_2'('#skF_4'))
    | '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5327,c_22])).

tff(c_5398,plain,
    ( r2_hidden('#skF_3'('#skF_4'),'#skF_2'('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_130,c_5368])).

tff(c_5411,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5398])).

tff(c_5423,plain,(
    v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_5411])).

tff(c_5436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_5423])).

tff(c_5437,plain,(
    r2_hidden('#skF_3'('#skF_4'),'#skF_2'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5398])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_3'(A_8),'#skF_2'(A_8))
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5490,plain,(
    v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5437,c_18])).

tff(c_5508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_5490])).

tff(c_5510,plain,(
    ~ v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4443])).

tff(c_5519,plain,(
    ! [B_332] :
      ( '#skF_2'(k1_ordinal1(B_332)) = B_332
      | r2_hidden('#skF_2'(k1_ordinal1(B_332)),B_332)
      | v2_ordinal1(k1_ordinal1(B_332)) ) ),
    inference(resolution,[status(thm)],[c_26,c_268])).

tff(c_5543,plain,
    ( v3_ordinal1('#skF_2'(k1_ordinal1('#skF_4')))
    | '#skF_2'(k1_ordinal1('#skF_4')) = '#skF_4'
    | v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5519,c_50])).

tff(c_5555,plain,
    ( v3_ordinal1('#skF_2'(k1_ordinal1('#skF_4')))
    | '#skF_2'(k1_ordinal1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5510,c_5543])).

tff(c_5556,plain,(
    '#skF_2'(k1_ordinal1('#skF_4')) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5555])).

tff(c_20,plain,(
    ! [A_8] :
      ( '#skF_2'(A_8) != '#skF_3'(A_8)
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5517,plain,(
    '#skF_2'(k1_ordinal1('#skF_4')) != '#skF_3'(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_5510])).

tff(c_5557,plain,(
    '#skF_3'(k1_ordinal1('#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5556,c_5517])).

tff(c_288,plain,(
    ! [B_67] :
      ( '#skF_3'(k1_ordinal1(B_67)) = B_67
      | r2_hidden('#skF_3'(k1_ordinal1(B_67)),B_67)
      | v2_ordinal1(k1_ordinal1(B_67)) ) ),
    inference(resolution,[status(thm)],[c_24,c_268])).

tff(c_5573,plain,
    ( ~ r2_hidden('#skF_3'(k1_ordinal1('#skF_4')),'#skF_4')
    | v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5556,c_18])).

tff(c_5584,plain,(
    ~ r2_hidden('#skF_3'(k1_ordinal1('#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5510,c_5573])).

tff(c_5607,plain,
    ( '#skF_3'(k1_ordinal1('#skF_4')) = '#skF_4'
    | v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_288,c_5584])).

tff(c_5614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5510,c_5557,c_5607])).

tff(c_5616,plain,(
    '#skF_2'(k1_ordinal1('#skF_4')) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5555])).

tff(c_289,plain,(
    ! [B_67] :
      ( '#skF_2'(k1_ordinal1(B_67)) = B_67
      | r2_hidden('#skF_2'(k1_ordinal1(B_67)),B_67)
      | v2_ordinal1(k1_ordinal1(B_67)) ) ),
    inference(resolution,[status(thm)],[c_26,c_268])).

tff(c_5509,plain,
    ( '#skF_3'(k1_ordinal1('#skF_4')) = '#skF_4'
    | v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_4443])).

tff(c_5642,plain,(
    v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_5509])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_ordinal1(A_1)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5651,plain,(
    v1_ordinal1('#skF_3'(k1_ordinal1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_5642,c_4])).

tff(c_5615,plain,(
    v3_ordinal1('#skF_2'(k1_ordinal1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_5555])).

tff(c_318,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(B_71,A_72)
      | r1_ordinal1(A_72,B_71)
      | ~ v3_ordinal1(B_71)
      | ~ v3_ordinal1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_345,plain,(
    ! [A_8] :
      ( v2_ordinal1(A_8)
      | r1_ordinal1('#skF_3'(A_8),'#skF_2'(A_8))
      | ~ v3_ordinal1('#skF_2'(A_8))
      | ~ v3_ordinal1('#skF_3'(A_8)) ) ),
    inference(resolution,[status(thm)],[c_318,c_22])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r1_ordinal1(A_15,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_31] :
      ( v3_ordinal1(k1_ordinal1(A_31))
      | ~ v3_ordinal1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    ! [B_18] : r2_hidden(B_18,k1_ordinal1(B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_360,plain,(
    ! [A_75,C_76,B_77] :
      ( r2_hidden(A_75,C_76)
      | ~ r2_hidden(B_77,C_76)
      | ~ r1_tarski(A_75,B_77)
      | ~ v3_ordinal1(C_76)
      | ~ v3_ordinal1(B_77)
      | ~ v1_ordinal1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5703,plain,(
    ! [A_343,B_344] :
      ( r2_hidden(A_343,k1_ordinal1(B_344))
      | ~ r1_tarski(A_343,B_344)
      | ~ v3_ordinal1(k1_ordinal1(B_344))
      | ~ v3_ordinal1(B_344)
      | ~ v1_ordinal1(A_343) ) ),
    inference(resolution,[status(thm)],[c_34,c_360])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( B_18 = A_17
      | r2_hidden(A_17,B_18)
      | ~ r2_hidden(A_17,k1_ordinal1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5870,plain,(
    ! [B_362,A_363] :
      ( B_362 = A_363
      | r2_hidden(A_363,B_362)
      | ~ r1_tarski(A_363,B_362)
      | ~ v3_ordinal1(k1_ordinal1(B_362))
      | ~ v3_ordinal1(B_362)
      | ~ v1_ordinal1(A_363) ) ),
    inference(resolution,[status(thm)],[c_5703,c_32])).

tff(c_5931,plain,(
    ! [A_368,A_367] :
      ( A_368 = A_367
      | r2_hidden(A_367,A_368)
      | ~ r1_tarski(A_367,A_368)
      | ~ v1_ordinal1(A_367)
      | ~ v3_ordinal1(A_368) ) ),
    inference(resolution,[status(thm)],[c_44,c_5870])).

tff(c_6143,plain,(
    ! [A_381] :
      ( v2_ordinal1(A_381)
      | '#skF_2'(A_381) = '#skF_3'(A_381)
      | ~ r1_tarski('#skF_3'(A_381),'#skF_2'(A_381))
      | ~ v1_ordinal1('#skF_3'(A_381))
      | ~ v3_ordinal1('#skF_2'(A_381)) ) ),
    inference(resolution,[status(thm)],[c_5931,c_18])).

tff(c_7872,plain,(
    ! [A_470] :
      ( v2_ordinal1(A_470)
      | '#skF_2'(A_470) = '#skF_3'(A_470)
      | ~ v1_ordinal1('#skF_3'(A_470))
      | ~ r1_ordinal1('#skF_3'(A_470),'#skF_2'(A_470))
      | ~ v3_ordinal1('#skF_2'(A_470))
      | ~ v3_ordinal1('#skF_3'(A_470)) ) ),
    inference(resolution,[status(thm)],[c_30,c_6143])).

tff(c_7915,plain,(
    ! [A_471] :
      ( '#skF_2'(A_471) = '#skF_3'(A_471)
      | ~ v1_ordinal1('#skF_3'(A_471))
      | v2_ordinal1(A_471)
      | ~ v3_ordinal1('#skF_2'(A_471))
      | ~ v3_ordinal1('#skF_3'(A_471)) ) ),
    inference(resolution,[status(thm)],[c_345,c_7872])).

tff(c_7918,plain,
    ( '#skF_2'(k1_ordinal1('#skF_4')) = '#skF_3'(k1_ordinal1('#skF_4'))
    | ~ v1_ordinal1('#skF_3'(k1_ordinal1('#skF_4')))
    | v2_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_5615,c_7915])).

tff(c_7930,plain,
    ( '#skF_2'(k1_ordinal1('#skF_4')) = '#skF_3'(k1_ordinal1('#skF_4'))
    | v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5642,c_5651,c_7918])).

tff(c_7932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5510,c_5517,c_7930])).

tff(c_7933,plain,(
    '#skF_3'(k1_ordinal1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5509])).

tff(c_7951,plain,
    ( ~ r2_hidden('#skF_2'(k1_ordinal1('#skF_4')),'#skF_4')
    | v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7933,c_22])).

tff(c_7967,plain,(
    ~ r2_hidden('#skF_2'(k1_ordinal1('#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5510,c_7951])).

tff(c_7975,plain,
    ( '#skF_2'(k1_ordinal1('#skF_4')) = '#skF_4'
    | v2_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_289,c_7967])).

tff(c_7982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5510,c_5616,c_7975])).

tff(c_7984,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_14,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | v1_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [B_42] :
      ( r1_tarski(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_77,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_8044,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_7984,c_77])).

tff(c_12,plain,(
    ! [A_4] :
      ( ~ r1_tarski('#skF_1'(A_4),A_4)
      | v1_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8047,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8044,c_12])).

tff(c_8051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7984,c_8047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.04/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/3.04  
% 8.04/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/3.04  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 8.04/3.04  
% 8.04/3.04  %Foreground sorts:
% 8.04/3.04  
% 8.04/3.04  
% 8.04/3.04  %Background operators:
% 8.04/3.04  
% 8.04/3.04  
% 8.04/3.04  %Foreground operators:
% 8.04/3.04  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.04/3.04  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 8.04/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.04/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.04/3.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.04/3.04  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 8.04/3.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.04/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.04/3.04  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 8.04/3.04  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 8.04/3.04  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 8.04/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.04/3.04  tff('#skF_4', type, '#skF_4': $i).
% 8.04/3.04  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.04/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.04/3.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.04/3.04  
% 8.04/3.06  tff(f_46, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 8.04/3.06  tff(f_120, negated_conjecture, ~(![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_ordinal1)).
% 8.04/3.06  tff(f_63, axiom, (![A]: (v2_ordinal1(A) <=> (![B, C]: ~((((r2_hidden(B, A) & r2_hidden(C, A)) & ~r2_hidden(B, C)) & ~(B = C)) & ~r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_ordinal1)).
% 8.04/3.06  tff(f_37, axiom, (![A]: ((v1_ordinal1(A) & v2_ordinal1(A)) => v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_ordinal1)).
% 8.04/3.06  tff(f_77, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 8.04/3.06  tff(f_31, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 8.04/3.06  tff(f_106, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 8.04/3.06  tff(f_71, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.04/3.06  tff(f_110, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 8.04/3.06  tff(f_91, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 8.04/3.06  tff(c_66, plain, (![A_41]: (r2_hidden('#skF_1'(A_41), A_41) | v1_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.04/3.06  tff(c_50, plain, (![B_33]: (v3_ordinal1(B_33) | ~r2_hidden(B_33, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.04/3.06  tff(c_71, plain, (v3_ordinal1('#skF_1'('#skF_4')) | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_50])).
% 8.04/3.06  tff(c_78, plain, (v1_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_71])).
% 8.04/3.06  tff(c_79, plain, (![A_43]: (r2_hidden('#skF_2'(A_43), A_43) | v2_ordinal1(A_43))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_89, plain, (v3_ordinal1('#skF_2'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_79, c_50])).
% 8.04/3.06  tff(c_90, plain, (v2_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_89])).
% 8.04/3.06  tff(c_113, plain, (![A_46]: (v3_ordinal1(A_46) | ~v2_ordinal1(A_46) | ~v1_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.04/3.06  tff(c_46, plain, (~v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.04/3.06  tff(c_122, plain, (~v2_ordinal1('#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_113, c_46])).
% 8.04/3.06  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_90, c_122])).
% 8.04/3.06  tff(c_130, plain, (~v2_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_89])).
% 8.04/3.06  tff(c_26, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | v2_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_140, plain, (![A_47]: ('#skF_2'(A_47)!='#skF_3'(A_47) | v2_ordinal1(A_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_144, plain, ('#skF_2'('#skF_4')!='#skF_3'('#skF_4')), inference(resolution, [status(thm)], [c_140, c_130])).
% 8.04/3.06  tff(c_24, plain, (![A_8]: (r2_hidden('#skF_3'(A_8), A_8) | v2_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_268, plain, (![B_67, A_68]: (B_67=A_68 | r2_hidden(A_68, B_67) | ~r2_hidden(A_68, k1_ordinal1(B_67)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.04/3.06  tff(c_4411, plain, (![B_263]: ('#skF_3'(k1_ordinal1(B_263))=B_263 | r2_hidden('#skF_3'(k1_ordinal1(B_263)), B_263) | v2_ordinal1(k1_ordinal1(B_263)))), inference(resolution, [status(thm)], [c_24, c_268])).
% 8.04/3.06  tff(c_4443, plain, (v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4'))) | '#skF_3'(k1_ordinal1('#skF_4'))='#skF_4' | v2_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_4411, c_50])).
% 8.04/3.06  tff(c_4444, plain, (v2_ordinal1(k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4443])).
% 8.04/3.06  tff(c_36, plain, (![A_17, B_18]: (~r2_hidden(A_17, B_18) | r2_hidden(A_17, k1_ordinal1(B_18)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.04/3.06  tff(c_431, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | C_85=B_86 | r2_hidden(B_86, C_85) | ~r2_hidden(C_85, A_87) | ~r2_hidden(B_86, A_87) | ~v2_ordinal1(A_87))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_5200, plain, (![A_322, B_323, B_324]: (r2_hidden(A_322, B_323) | B_323=A_322 | r2_hidden(B_323, A_322) | ~r2_hidden(B_323, k1_ordinal1(B_324)) | ~v2_ordinal1(k1_ordinal1(B_324)) | ~r2_hidden(A_322, B_324))), inference(resolution, [status(thm)], [c_36, c_431])).
% 8.04/3.06  tff(c_5250, plain, (![A_325, A_326, B_327]: (r2_hidden(A_325, A_326) | A_326=A_325 | r2_hidden(A_326, A_325) | ~v2_ordinal1(k1_ordinal1(B_327)) | ~r2_hidden(A_325, B_327) | ~r2_hidden(A_326, B_327))), inference(resolution, [status(thm)], [c_36, c_5200])).
% 8.04/3.06  tff(c_5261, plain, (![A_328, A_329]: (r2_hidden(A_328, A_329) | A_329=A_328 | r2_hidden(A_329, A_328) | ~r2_hidden(A_328, '#skF_4') | ~r2_hidden(A_329, '#skF_4'))), inference(resolution, [status(thm)], [c_4444, c_5250])).
% 8.04/3.06  tff(c_5285, plain, (![A_329]: (r2_hidden('#skF_3'('#skF_4'), A_329) | A_329='#skF_3'('#skF_4') | r2_hidden(A_329, '#skF_3'('#skF_4')) | ~r2_hidden(A_329, '#skF_4') | v2_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_5261])).
% 8.04/3.06  tff(c_5327, plain, (![A_330]: (r2_hidden('#skF_3'('#skF_4'), A_330) | A_330='#skF_3'('#skF_4') | r2_hidden(A_330, '#skF_3'('#skF_4')) | ~r2_hidden(A_330, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_130, c_5285])).
% 8.04/3.06  tff(c_22, plain, (![A_8]: (~r2_hidden('#skF_2'(A_8), '#skF_3'(A_8)) | v2_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_5368, plain, (v2_ordinal1('#skF_4') | r2_hidden('#skF_3'('#skF_4'), '#skF_2'('#skF_4')) | '#skF_2'('#skF_4')='#skF_3'('#skF_4') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_5327, c_22])).
% 8.04/3.06  tff(c_5398, plain, (r2_hidden('#skF_3'('#skF_4'), '#skF_2'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_144, c_130, c_5368])).
% 8.04/3.06  tff(c_5411, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5398])).
% 8.04/3.06  tff(c_5423, plain, (v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_5411])).
% 8.04/3.06  tff(c_5436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_5423])).
% 8.04/3.06  tff(c_5437, plain, (r2_hidden('#skF_3'('#skF_4'), '#skF_2'('#skF_4'))), inference(splitRight, [status(thm)], [c_5398])).
% 8.04/3.06  tff(c_18, plain, (![A_8]: (~r2_hidden('#skF_3'(A_8), '#skF_2'(A_8)) | v2_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_5490, plain, (v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_5437, c_18])).
% 8.04/3.06  tff(c_5508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_5490])).
% 8.04/3.06  tff(c_5510, plain, (~v2_ordinal1(k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_4443])).
% 8.04/3.06  tff(c_5519, plain, (![B_332]: ('#skF_2'(k1_ordinal1(B_332))=B_332 | r2_hidden('#skF_2'(k1_ordinal1(B_332)), B_332) | v2_ordinal1(k1_ordinal1(B_332)))), inference(resolution, [status(thm)], [c_26, c_268])).
% 8.04/3.06  tff(c_5543, plain, (v3_ordinal1('#skF_2'(k1_ordinal1('#skF_4'))) | '#skF_2'(k1_ordinal1('#skF_4'))='#skF_4' | v2_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_5519, c_50])).
% 8.04/3.06  tff(c_5555, plain, (v3_ordinal1('#skF_2'(k1_ordinal1('#skF_4'))) | '#skF_2'(k1_ordinal1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5510, c_5543])).
% 8.04/3.06  tff(c_5556, plain, ('#skF_2'(k1_ordinal1('#skF_4'))='#skF_4'), inference(splitLeft, [status(thm)], [c_5555])).
% 8.04/3.06  tff(c_20, plain, (![A_8]: ('#skF_2'(A_8)!='#skF_3'(A_8) | v2_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.04/3.06  tff(c_5517, plain, ('#skF_2'(k1_ordinal1('#skF_4'))!='#skF_3'(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_5510])).
% 8.04/3.06  tff(c_5557, plain, ('#skF_3'(k1_ordinal1('#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5556, c_5517])).
% 8.04/3.06  tff(c_288, plain, (![B_67]: ('#skF_3'(k1_ordinal1(B_67))=B_67 | r2_hidden('#skF_3'(k1_ordinal1(B_67)), B_67) | v2_ordinal1(k1_ordinal1(B_67)))), inference(resolution, [status(thm)], [c_24, c_268])).
% 8.04/3.06  tff(c_5573, plain, (~r2_hidden('#skF_3'(k1_ordinal1('#skF_4')), '#skF_4') | v2_ordinal1(k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5556, c_18])).
% 8.04/3.06  tff(c_5584, plain, (~r2_hidden('#skF_3'(k1_ordinal1('#skF_4')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5510, c_5573])).
% 8.04/3.06  tff(c_5607, plain, ('#skF_3'(k1_ordinal1('#skF_4'))='#skF_4' | v2_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_288, c_5584])).
% 8.04/3.06  tff(c_5614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5510, c_5557, c_5607])).
% 8.04/3.06  tff(c_5616, plain, ('#skF_2'(k1_ordinal1('#skF_4'))!='#skF_4'), inference(splitRight, [status(thm)], [c_5555])).
% 8.04/3.06  tff(c_289, plain, (![B_67]: ('#skF_2'(k1_ordinal1(B_67))=B_67 | r2_hidden('#skF_2'(k1_ordinal1(B_67)), B_67) | v2_ordinal1(k1_ordinal1(B_67)))), inference(resolution, [status(thm)], [c_26, c_268])).
% 8.04/3.06  tff(c_5509, plain, ('#skF_3'(k1_ordinal1('#skF_4'))='#skF_4' | v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4')))), inference(splitRight, [status(thm)], [c_4443])).
% 8.04/3.06  tff(c_5642, plain, (v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4')))), inference(splitLeft, [status(thm)], [c_5509])).
% 8.04/3.06  tff(c_4, plain, (![A_1]: (v1_ordinal1(A_1) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.04/3.06  tff(c_5651, plain, (v1_ordinal1('#skF_3'(k1_ordinal1('#skF_4')))), inference(resolution, [status(thm)], [c_5642, c_4])).
% 8.04/3.06  tff(c_5615, plain, (v3_ordinal1('#skF_2'(k1_ordinal1('#skF_4')))), inference(splitRight, [status(thm)], [c_5555])).
% 8.04/3.06  tff(c_318, plain, (![B_71, A_72]: (r2_hidden(B_71, A_72) | r1_ordinal1(A_72, B_71) | ~v3_ordinal1(B_71) | ~v3_ordinal1(A_72))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.04/3.06  tff(c_345, plain, (![A_8]: (v2_ordinal1(A_8) | r1_ordinal1('#skF_3'(A_8), '#skF_2'(A_8)) | ~v3_ordinal1('#skF_2'(A_8)) | ~v3_ordinal1('#skF_3'(A_8)))), inference(resolution, [status(thm)], [c_318, c_22])).
% 8.04/3.06  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r1_ordinal1(A_15, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.04/3.06  tff(c_44, plain, (![A_31]: (v3_ordinal1(k1_ordinal1(A_31)) | ~v3_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.04/3.06  tff(c_34, plain, (![B_18]: (r2_hidden(B_18, k1_ordinal1(B_18)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.04/3.06  tff(c_360, plain, (![A_75, C_76, B_77]: (r2_hidden(A_75, C_76) | ~r2_hidden(B_77, C_76) | ~r1_tarski(A_75, B_77) | ~v3_ordinal1(C_76) | ~v3_ordinal1(B_77) | ~v1_ordinal1(A_75))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.04/3.06  tff(c_5703, plain, (![A_343, B_344]: (r2_hidden(A_343, k1_ordinal1(B_344)) | ~r1_tarski(A_343, B_344) | ~v3_ordinal1(k1_ordinal1(B_344)) | ~v3_ordinal1(B_344) | ~v1_ordinal1(A_343))), inference(resolution, [status(thm)], [c_34, c_360])).
% 8.04/3.06  tff(c_32, plain, (![B_18, A_17]: (B_18=A_17 | r2_hidden(A_17, B_18) | ~r2_hidden(A_17, k1_ordinal1(B_18)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.04/3.06  tff(c_5870, plain, (![B_362, A_363]: (B_362=A_363 | r2_hidden(A_363, B_362) | ~r1_tarski(A_363, B_362) | ~v3_ordinal1(k1_ordinal1(B_362)) | ~v3_ordinal1(B_362) | ~v1_ordinal1(A_363))), inference(resolution, [status(thm)], [c_5703, c_32])).
% 8.04/3.06  tff(c_5931, plain, (![A_368, A_367]: (A_368=A_367 | r2_hidden(A_367, A_368) | ~r1_tarski(A_367, A_368) | ~v1_ordinal1(A_367) | ~v3_ordinal1(A_368))), inference(resolution, [status(thm)], [c_44, c_5870])).
% 8.04/3.06  tff(c_6143, plain, (![A_381]: (v2_ordinal1(A_381) | '#skF_2'(A_381)='#skF_3'(A_381) | ~r1_tarski('#skF_3'(A_381), '#skF_2'(A_381)) | ~v1_ordinal1('#skF_3'(A_381)) | ~v3_ordinal1('#skF_2'(A_381)))), inference(resolution, [status(thm)], [c_5931, c_18])).
% 8.04/3.06  tff(c_7872, plain, (![A_470]: (v2_ordinal1(A_470) | '#skF_2'(A_470)='#skF_3'(A_470) | ~v1_ordinal1('#skF_3'(A_470)) | ~r1_ordinal1('#skF_3'(A_470), '#skF_2'(A_470)) | ~v3_ordinal1('#skF_2'(A_470)) | ~v3_ordinal1('#skF_3'(A_470)))), inference(resolution, [status(thm)], [c_30, c_6143])).
% 8.04/3.06  tff(c_7915, plain, (![A_471]: ('#skF_2'(A_471)='#skF_3'(A_471) | ~v1_ordinal1('#skF_3'(A_471)) | v2_ordinal1(A_471) | ~v3_ordinal1('#skF_2'(A_471)) | ~v3_ordinal1('#skF_3'(A_471)))), inference(resolution, [status(thm)], [c_345, c_7872])).
% 8.04/3.06  tff(c_7918, plain, ('#skF_2'(k1_ordinal1('#skF_4'))='#skF_3'(k1_ordinal1('#skF_4')) | ~v1_ordinal1('#skF_3'(k1_ordinal1('#skF_4'))) | v2_ordinal1(k1_ordinal1('#skF_4')) | ~v3_ordinal1('#skF_3'(k1_ordinal1('#skF_4')))), inference(resolution, [status(thm)], [c_5615, c_7915])).
% 8.04/3.06  tff(c_7930, plain, ('#skF_2'(k1_ordinal1('#skF_4'))='#skF_3'(k1_ordinal1('#skF_4')) | v2_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5642, c_5651, c_7918])).
% 8.04/3.06  tff(c_7932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5510, c_5517, c_7930])).
% 8.04/3.06  tff(c_7933, plain, ('#skF_3'(k1_ordinal1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_5509])).
% 8.04/3.06  tff(c_7951, plain, (~r2_hidden('#skF_2'(k1_ordinal1('#skF_4')), '#skF_4') | v2_ordinal1(k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7933, c_22])).
% 8.04/3.06  tff(c_7967, plain, (~r2_hidden('#skF_2'(k1_ordinal1('#skF_4')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5510, c_7951])).
% 8.04/3.06  tff(c_7975, plain, ('#skF_2'(k1_ordinal1('#skF_4'))='#skF_4' | v2_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_289, c_7967])).
% 8.04/3.06  tff(c_7982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5510, c_5616, c_7975])).
% 8.04/3.06  tff(c_7984, plain, (~v1_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_71])).
% 8.04/3.06  tff(c_14, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | v1_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.04/3.06  tff(c_72, plain, (![B_42]: (r1_tarski(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.04/3.06  tff(c_77, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4') | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_72])).
% 8.04/3.06  tff(c_8044, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_7984, c_77])).
% 8.04/3.06  tff(c_12, plain, (![A_4]: (~r1_tarski('#skF_1'(A_4), A_4) | v1_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.04/3.06  tff(c_8047, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_8044, c_12])).
% 8.04/3.06  tff(c_8051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7984, c_8047])).
% 8.04/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/3.06  
% 8.04/3.06  Inference rules
% 8.04/3.06  ----------------------
% 8.04/3.06  #Ref     : 0
% 8.04/3.06  #Sup     : 1892
% 8.04/3.06  #Fact    : 34
% 8.04/3.06  #Define  : 0
% 8.04/3.06  #Split   : 26
% 8.04/3.06  #Chain   : 0
% 8.04/3.06  #Close   : 0
% 8.24/3.06  
% 8.24/3.06  Ordering : KBO
% 8.24/3.06  
% 8.24/3.06  Simplification rules
% 8.24/3.06  ----------------------
% 8.24/3.06  #Subsume      : 646
% 8.24/3.06  #Demod        : 343
% 8.24/3.06  #Tautology    : 242
% 8.24/3.06  #SimpNegUnit  : 157
% 8.24/3.06  #BackRed      : 21
% 8.24/3.06  
% 8.24/3.06  #Partial instantiations: 0
% 8.24/3.06  #Strategies tried      : 1
% 8.24/3.06  
% 8.24/3.06  Timing (in seconds)
% 8.24/3.06  ----------------------
% 8.24/3.06  Preprocessing        : 0.31
% 8.24/3.06  Parsing              : 0.16
% 8.24/3.06  CNF conversion       : 0.02
% 8.24/3.06  Main loop            : 1.97
% 8.24/3.06  Inferencing          : 0.51
% 8.24/3.06  Reduction            : 0.44
% 8.24/3.06  Demodulation         : 0.29
% 8.24/3.06  BG Simplification    : 0.06
% 8.24/3.06  Subsumption          : 0.84
% 8.24/3.06  Abstraction          : 0.08
% 8.24/3.06  MUC search           : 0.00
% 8.24/3.06  Cooper               : 0.00
% 8.24/3.06  Total                : 2.32
% 8.24/3.06  Index Insertion      : 0.00
% 8.24/3.06  Index Deletion       : 0.00
% 8.24/3.06  Index Matching       : 0.00
% 8.24/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
