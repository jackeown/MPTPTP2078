%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0747+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:48 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  108 ( 236 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_ordinal1(A) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_87,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(c_552,plain,(
    ! [A_89] :
      ( '#skF_2'(A_89) != '#skF_3'(A_89)
      | v2_ordinal1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_1'(A_34),A_34)
      | v1_ordinal1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [B_26] :
      ( v3_ordinal1(B_26)
      | ~ r2_hidden(B_26,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_72,plain,
    ( v3_ordinal1('#skF_1'('#skF_5'))
    | v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_34])).

tff(c_73,plain,(
    v1_ordinal1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_53,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_2'(A_32),A_32)
      | v2_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_61,plain,
    ( v3_ordinal1('#skF_2'('#skF_5'))
    | v2_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_53,c_34])).

tff(c_62,plain,(
    v2_ordinal1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_84,plain,(
    ! [A_36] :
      ( v3_ordinal1(A_36)
      | ~ v2_ordinal1(A_36)
      | ~ v1_ordinal1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_26] :
      ( r2_hidden(B_26,'#skF_5')
      | ~ v3_ordinal1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_43,plain,(
    ! [B_29,A_30] :
      ( ~ r2_hidden(B_29,A_30)
      | ~ r2_hidden(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [B_31] :
      ( ~ r2_hidden('#skF_5',B_31)
      | ~ v3_ordinal1(B_31) ) ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_52,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_87,plain,
    ( ~ v2_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_52])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_62,c_87])).

tff(c_93,plain,(
    ~ v1_ordinal1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_92,plain,(
    v3_ordinal1('#skF_1'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_170,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_4'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( v3_ordinal1(A_20)
      | ~ r2_hidden(A_20,B_21)
      | ~ v3_ordinal1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_512,plain,(
    ! [A_83,B_84] :
      ( v3_ordinal1('#skF_4'(A_83,B_84))
      | ~ v3_ordinal1(A_83)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_170,c_30])).

tff(c_134,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_4'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_47,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_134])).

tff(c_518,plain,(
    ! [A_85] :
      ( ~ v3_ordinal1(A_85)
      | r1_tarski(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_512,c_139])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ r1_tarski('#skF_1'(A_4),A_4)
      | v1_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_522,plain,
    ( v1_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_518,c_8])).

tff(c_525,plain,(
    v1_ordinal1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_522])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_525])).

tff(c_529,plain,(
    ~ v2_ordinal1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_556,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(resolution,[status(thm)],[c_552,c_529])).

tff(c_541,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_3'(A_88),A_88)
      | v2_ordinal1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_547,plain,
    ( v3_ordinal1('#skF_3'('#skF_5'))
    | v2_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_541,c_34])).

tff(c_551,plain,(
    v3_ordinal1('#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_529,c_547])).

tff(c_528,plain,(
    v3_ordinal1('#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_756,plain,(
    ! [B_121,A_122] :
      ( r2_hidden(B_121,A_122)
      | B_121 = A_122
      | r2_hidden(A_122,B_121)
      | ~ v3_ordinal1(B_121)
      | ~ v3_ordinal1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2'(A_8),'#skF_3'(A_8))
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2211,plain,(
    ! [A_233] :
      ( v2_ordinal1(A_233)
      | '#skF_2'(A_233) = '#skF_3'(A_233)
      | r2_hidden('#skF_3'(A_233),'#skF_2'(A_233))
      | ~ v3_ordinal1('#skF_2'(A_233))
      | ~ v3_ordinal1('#skF_3'(A_233)) ) ),
    inference(resolution,[status(thm)],[c_756,c_18])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_3'(A_8),'#skF_2'(A_8))
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2892,plain,(
    ! [A_264] :
      ( v2_ordinal1(A_264)
      | '#skF_2'(A_264) = '#skF_3'(A_264)
      | ~ v3_ordinal1('#skF_2'(A_264))
      | ~ v3_ordinal1('#skF_3'(A_264)) ) ),
    inference(resolution,[status(thm)],[c_2211,c_14])).

tff(c_2904,plain,
    ( v2_ordinal1('#skF_5')
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ v3_ordinal1('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_528,c_2892])).

tff(c_2910,plain,
    ( v2_ordinal1('#skF_5')
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_2904])).

tff(c_2912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_556,c_529,c_2910])).

%------------------------------------------------------------------------------
