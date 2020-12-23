%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  124 (1810 expanded)
%              Number of leaves         :   32 ( 662 expanded)
%              Depth                    :   25
%              Number of atoms          :  228 (6794 expanded)
%              Number of equality atoms :   53 (2273 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = k1_relat_1(C)
                & k2_relat_1(B) = k1_tarski(A)
                & k2_relat_1(C) = k1_tarski(A) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_153,plain,(
    ! [A_103,B_104] :
      ( r2_hidden(k4_tarski('#skF_3'(A_103,B_104),'#skF_4'(A_103,B_104)),A_103)
      | r1_tarski(A_103,B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    ! [C_73,A_71,B_72] :
      ( k1_funct_1(C_73,A_71) = B_72
      | ~ r2_hidden(k4_tarski(A_71,B_72),C_73)
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_406,plain,(
    ! [A_126,B_127] :
      ( k1_funct_1(A_126,'#skF_3'(A_126,B_127)) = '#skF_4'(A_126,B_127)
      | ~ v1_funct_1(A_126)
      | r1_tarski(A_126,B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_153,c_52])).

tff(c_54,plain,(
    ! [A_71,C_73,B_72] :
      ( r2_hidden(A_71,k1_relat_1(C_73))
      | ~ r2_hidden(k4_tarski(A_71,B_72),C_73)
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_171,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_3'(A_103,B_104),k1_relat_1(A_103))
      | ~ v1_funct_1(A_103)
      | r1_tarski(A_103,B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_153,c_54])).

tff(c_60,plain,(
    k2_relat_1('#skF_10') = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_180,plain,(
    ! [A_108,D_109] :
      ( r2_hidden(k1_funct_1(A_108,D_109),k2_relat_1(A_108))
      | ~ r2_hidden(D_109,k1_relat_1(A_108))
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_183,plain,(
    ! [D_109] :
      ( r2_hidden(k1_funct_1('#skF_10',D_109),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_109,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_180])).

tff(c_191,plain,(
    ! [D_110] :
      ( r2_hidden(k1_funct_1('#skF_10',D_110),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_110,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_183])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_196,plain,(
    ! [D_111] :
      ( k1_funct_1('#skF_10',D_111) = '#skF_9'
      | ~ r2_hidden(D_111,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_191,c_8])).

tff(c_203,plain,(
    ! [B_104] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_104)) = '#skF_9'
      | ~ v1_funct_1('#skF_10')
      | r1_tarski('#skF_10',B_104)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_171,c_196])).

tff(c_219,plain,(
    ! [B_104] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_104)) = '#skF_9'
      | r1_tarski('#skF_10',B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_203])).

tff(c_420,plain,(
    ! [B_127] :
      ( '#skF_4'('#skF_10',B_127) = '#skF_9'
      | r1_tarski('#skF_10',B_127)
      | ~ v1_funct_1('#skF_10')
      | r1_tarski('#skF_10',B_127)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_219])).

tff(c_445,plain,(
    ! [B_127] :
      ( '#skF_4'('#skF_10',B_127) = '#skF_9'
      | r1_tarski('#skF_10',B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_420])).

tff(c_66,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    k1_relat_1('#skF_11') = k1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_173,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_3'(A_105,B_106),k1_relat_1(A_105))
      | ~ v1_funct_1(A_105)
      | r1_tarski(A_105,B_106)
      | ~ v1_relat_1(A_105) ) ),
    inference(resolution,[status(thm)],[c_153,c_54])).

tff(c_176,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_3'('#skF_11',B_106),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_11')
      | r1_tarski('#skF_11',B_106)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_173])).

tff(c_178,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_3'('#skF_11',B_106),k1_relat_1('#skF_10'))
      | r1_tarski('#skF_11',B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_176])).

tff(c_58,plain,(
    k2_relat_1('#skF_11') = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_186,plain,(
    ! [D_109] :
      ( r2_hidden(k1_funct_1('#skF_11',D_109),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_109,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_180])).

tff(c_241,plain,(
    ! [D_113] :
      ( r2_hidden(k1_funct_1('#skF_11',D_113),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_113,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_186])).

tff(c_246,plain,(
    ! [D_114] :
      ( k1_funct_1('#skF_11',D_114) = '#skF_9'
      | ~ r2_hidden(D_114,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_241,c_8])).

tff(c_266,plain,(
    ! [B_106] :
      ( k1_funct_1('#skF_11','#skF_3'('#skF_11',B_106)) = '#skF_9'
      | r1_tarski('#skF_11',B_106) ) ),
    inference(resolution,[status(thm)],[c_178,c_246])).

tff(c_416,plain,(
    ! [B_127] :
      ( '#skF_4'('#skF_11',B_127) = '#skF_9'
      | r1_tarski('#skF_11',B_127)
      | ~ v1_funct_1('#skF_11')
      | r1_tarski('#skF_11',B_127)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_266])).

tff(c_455,plain,(
    ! [B_128] :
      ( '#skF_4'('#skF_11',B_128) = '#skF_9'
      | r1_tarski('#skF_11',B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_416])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_476,plain,(
    ! [B_132] :
      ( B_132 = '#skF_11'
      | ~ r1_tarski(B_132,'#skF_11')
      | '#skF_4'('#skF_11',B_132) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_480,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_4'('#skF_11','#skF_10') = '#skF_9'
    | '#skF_4'('#skF_10','#skF_11') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_445,c_476])).

tff(c_491,plain,
    ( '#skF_4'('#skF_11','#skF_10') = '#skF_9'
    | '#skF_4'('#skF_10','#skF_11') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_480])).

tff(c_533,plain,(
    '#skF_4'('#skF_10','#skF_11') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_30,plain,(
    ! [A_14,B_24] :
      ( r2_hidden(k4_tarski('#skF_3'(A_14,B_24),'#skF_4'(A_14,B_24)),A_14)
      | r1_tarski(A_14,B_24)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_540,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_11'),'#skF_9'),'#skF_10')
    | r1_tarski('#skF_10','#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_30])).

tff(c_548,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_11'),'#skF_9'),'#skF_10')
    | r1_tarski('#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_540])).

tff(c_594,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_599,plain,
    ( '#skF_11' = '#skF_10'
    | ~ r1_tarski('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_594,c_2])).

tff(c_605,plain,(
    ~ r1_tarski('#skF_11','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_599])).

tff(c_458,plain,(
    ! [B_128] :
      ( B_128 = '#skF_11'
      | ~ r1_tarski(B_128,'#skF_11')
      | '#skF_4'('#skF_11',B_128) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_597,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_4'('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_594,c_458])).

tff(c_602,plain,(
    '#skF_4'('#skF_11','#skF_10') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_597])).

tff(c_28,plain,(
    ! [A_14,B_24] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_14,B_24),'#skF_4'(A_14,B_24)),B_24)
      | r1_tarski(A_14,B_24)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_616,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10')
    | r1_tarski('#skF_11','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_28])).

tff(c_623,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10')
    | r1_tarski('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_616])).

tff(c_624,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_623])).

tff(c_613,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_11')
    | r1_tarski('#skF_11','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_30])).

tff(c_620,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_11')
    | r1_tarski('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_613])).

tff(c_621,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_620])).

tff(c_664,plain,
    ( r2_hidden('#skF_3'('#skF_11','#skF_10'),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_621,c_54])).

tff(c_673,plain,(
    r2_hidden('#skF_3'('#skF_11','#skF_10'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_664])).

tff(c_195,plain,(
    ! [D_110] :
      ( k1_funct_1('#skF_10',D_110) = '#skF_9'
      | ~ r2_hidden(D_110,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_191,c_8])).

tff(c_722,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_11','#skF_10')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_673,c_195])).

tff(c_50,plain,(
    ! [A_71,C_73] :
      ( r2_hidden(k4_tarski(A_71,k1_funct_1(C_73,A_71)),C_73)
      | ~ r2_hidden(A_71,k1_relat_1(C_73))
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_726,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_3'('#skF_11','#skF_10'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_50])).

tff(c_742,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_673,c_726])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_742])).

tff(c_746,plain,(
    ~ r1_tarski('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_745,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_11'),'#skF_9'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_759,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_11'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_745,c_54])).

tff(c_768,plain,(
    r2_hidden('#skF_3'('#skF_10','#skF_11'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_759])).

tff(c_245,plain,(
    ! [D_113] :
      ( k1_funct_1('#skF_11',D_113) = '#skF_9'
      | ~ r2_hidden(D_113,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_241,c_8])).

tff(c_815,plain,(
    k1_funct_1('#skF_11','#skF_3'('#skF_10','#skF_11')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_768,c_245])).

tff(c_851,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_11'),'#skF_9'),'#skF_11')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_11'),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_50])).

tff(c_867,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_11'),'#skF_9'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_768,c_62,c_851])).

tff(c_543,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_11'),'#skF_9'),'#skF_11')
    | r1_tarski('#skF_10','#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_28])).

tff(c_550,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_11'),'#skF_9'),'#skF_11')
    | r1_tarski('#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_543])).

tff(c_895,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_550])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_895])).

tff(c_898,plain,(
    '#skF_4'('#skF_10','#skF_11') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_897,plain,(
    '#skF_4'('#skF_11','#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_902,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_11')
    | r1_tarski('#skF_11','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_30])).

tff(c_909,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_11')
    | r1_tarski('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_902])).

tff(c_933,plain,(
    r1_tarski('#skF_11','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_909])).

tff(c_467,plain,(
    ! [B_130] :
      ( '#skF_4'('#skF_10',B_130) = '#skF_9'
      | r1_tarski('#skF_10',B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_420])).

tff(c_470,plain,(
    ! [B_130] :
      ( B_130 = '#skF_10'
      | ~ r1_tarski(B_130,'#skF_10')
      | '#skF_4'('#skF_10',B_130) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_467,c_2])).

tff(c_936,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_4'('#skF_10','#skF_11') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_933,c_470])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_898,c_56,c_936])).

tff(c_944,plain,(
    ~ r1_tarski('#skF_11','#skF_10') ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_943,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_987,plain,
    ( r2_hidden('#skF_3'('#skF_11','#skF_10'),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_943,c_54])).

tff(c_996,plain,(
    r2_hidden('#skF_3'('#skF_11','#skF_10'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_987])).

tff(c_1045,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_11','#skF_10')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_996,c_195])).

tff(c_1058,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_3'('#skF_11','#skF_10'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_50])).

tff(c_1074,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_996,c_1058])).

tff(c_905,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10')
    | r1_tarski('#skF_11','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_28])).

tff(c_911,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_10'),'#skF_9'),'#skF_10')
    | r1_tarski('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_905])).

tff(c_1102,plain,(
    r1_tarski('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_911])).

tff(c_1103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_944,c_1102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 19:28:49 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.31  
% 2.65/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.31  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 2.65/1.31  
% 2.65/1.31  %Foreground sorts:
% 2.65/1.31  
% 2.65/1.31  
% 2.65/1.31  %Background operators:
% 2.65/1.31  
% 2.65/1.31  
% 2.65/1.31  %Foreground operators:
% 2.65/1.31  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.65/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.31  tff('#skF_11', type, '#skF_11': $i).
% 2.65/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.65/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.65/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.31  tff('#skF_10', type, '#skF_10': $i).
% 2.65/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.65/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.65/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.31  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.65/1.31  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.65/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.65/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.65/1.31  
% 2.96/1.33  tff(f_97, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_1)).
% 2.96/1.33  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 2.96/1.33  tff(f_79, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.96/1.33  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.96/1.33  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.96/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.96/1.33  tff(c_56, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_70, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_68, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_153, plain, (![A_103, B_104]: (r2_hidden(k4_tarski('#skF_3'(A_103, B_104), '#skF_4'(A_103, B_104)), A_103) | r1_tarski(A_103, B_104) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.33  tff(c_52, plain, (![C_73, A_71, B_72]: (k1_funct_1(C_73, A_71)=B_72 | ~r2_hidden(k4_tarski(A_71, B_72), C_73) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.96/1.33  tff(c_406, plain, (![A_126, B_127]: (k1_funct_1(A_126, '#skF_3'(A_126, B_127))='#skF_4'(A_126, B_127) | ~v1_funct_1(A_126) | r1_tarski(A_126, B_127) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_153, c_52])).
% 2.96/1.33  tff(c_54, plain, (![A_71, C_73, B_72]: (r2_hidden(A_71, k1_relat_1(C_73)) | ~r2_hidden(k4_tarski(A_71, B_72), C_73) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.96/1.33  tff(c_171, plain, (![A_103, B_104]: (r2_hidden('#skF_3'(A_103, B_104), k1_relat_1(A_103)) | ~v1_funct_1(A_103) | r1_tarski(A_103, B_104) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_153, c_54])).
% 2.96/1.33  tff(c_60, plain, (k2_relat_1('#skF_10')=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_180, plain, (![A_108, D_109]: (r2_hidden(k1_funct_1(A_108, D_109), k2_relat_1(A_108)) | ~r2_hidden(D_109, k1_relat_1(A_108)) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.96/1.33  tff(c_183, plain, (![D_109]: (r2_hidden(k1_funct_1('#skF_10', D_109), k1_tarski('#skF_9')) | ~r2_hidden(D_109, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_180])).
% 2.96/1.33  tff(c_191, plain, (![D_110]: (r2_hidden(k1_funct_1('#skF_10', D_110), k1_tarski('#skF_9')) | ~r2_hidden(D_110, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_183])).
% 2.96/1.33  tff(c_8, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.33  tff(c_196, plain, (![D_111]: (k1_funct_1('#skF_10', D_111)='#skF_9' | ~r2_hidden(D_111, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_191, c_8])).
% 2.96/1.33  tff(c_203, plain, (![B_104]: (k1_funct_1('#skF_10', '#skF_3'('#skF_10', B_104))='#skF_9' | ~v1_funct_1('#skF_10') | r1_tarski('#skF_10', B_104) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_171, c_196])).
% 2.96/1.33  tff(c_219, plain, (![B_104]: (k1_funct_1('#skF_10', '#skF_3'('#skF_10', B_104))='#skF_9' | r1_tarski('#skF_10', B_104))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_203])).
% 2.96/1.33  tff(c_420, plain, (![B_127]: ('#skF_4'('#skF_10', B_127)='#skF_9' | r1_tarski('#skF_10', B_127) | ~v1_funct_1('#skF_10') | r1_tarski('#skF_10', B_127) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_219])).
% 2.96/1.33  tff(c_445, plain, (![B_127]: ('#skF_4'('#skF_10', B_127)='#skF_9' | r1_tarski('#skF_10', B_127))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_420])).
% 2.96/1.33  tff(c_66, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_64, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_62, plain, (k1_relat_1('#skF_11')=k1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_173, plain, (![A_105, B_106]: (r2_hidden('#skF_3'(A_105, B_106), k1_relat_1(A_105)) | ~v1_funct_1(A_105) | r1_tarski(A_105, B_106) | ~v1_relat_1(A_105))), inference(resolution, [status(thm)], [c_153, c_54])).
% 2.96/1.33  tff(c_176, plain, (![B_106]: (r2_hidden('#skF_3'('#skF_11', B_106), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_11') | r1_tarski('#skF_11', B_106) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_173])).
% 2.96/1.33  tff(c_178, plain, (![B_106]: (r2_hidden('#skF_3'('#skF_11', B_106), k1_relat_1('#skF_10')) | r1_tarski('#skF_11', B_106))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_176])).
% 2.96/1.33  tff(c_58, plain, (k2_relat_1('#skF_11')=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.33  tff(c_186, plain, (![D_109]: (r2_hidden(k1_funct_1('#skF_11', D_109), k1_tarski('#skF_9')) | ~r2_hidden(D_109, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_180])).
% 2.96/1.33  tff(c_241, plain, (![D_113]: (r2_hidden(k1_funct_1('#skF_11', D_113), k1_tarski('#skF_9')) | ~r2_hidden(D_113, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_186])).
% 2.96/1.33  tff(c_246, plain, (![D_114]: (k1_funct_1('#skF_11', D_114)='#skF_9' | ~r2_hidden(D_114, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_241, c_8])).
% 2.96/1.33  tff(c_266, plain, (![B_106]: (k1_funct_1('#skF_11', '#skF_3'('#skF_11', B_106))='#skF_9' | r1_tarski('#skF_11', B_106))), inference(resolution, [status(thm)], [c_178, c_246])).
% 2.96/1.33  tff(c_416, plain, (![B_127]: ('#skF_4'('#skF_11', B_127)='#skF_9' | r1_tarski('#skF_11', B_127) | ~v1_funct_1('#skF_11') | r1_tarski('#skF_11', B_127) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_266])).
% 2.96/1.33  tff(c_455, plain, (![B_128]: ('#skF_4'('#skF_11', B_128)='#skF_9' | r1_tarski('#skF_11', B_128))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_416])).
% 2.96/1.33  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.33  tff(c_476, plain, (![B_132]: (B_132='#skF_11' | ~r1_tarski(B_132, '#skF_11') | '#skF_4'('#skF_11', B_132)='#skF_9')), inference(resolution, [status(thm)], [c_455, c_2])).
% 2.96/1.33  tff(c_480, plain, ('#skF_11'='#skF_10' | '#skF_4'('#skF_11', '#skF_10')='#skF_9' | '#skF_4'('#skF_10', '#skF_11')='#skF_9'), inference(resolution, [status(thm)], [c_445, c_476])).
% 2.96/1.33  tff(c_491, plain, ('#skF_4'('#skF_11', '#skF_10')='#skF_9' | '#skF_4'('#skF_10', '#skF_11')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_56, c_480])).
% 2.96/1.33  tff(c_533, plain, ('#skF_4'('#skF_10', '#skF_11')='#skF_9'), inference(splitLeft, [status(thm)], [c_491])).
% 2.96/1.33  tff(c_30, plain, (![A_14, B_24]: (r2_hidden(k4_tarski('#skF_3'(A_14, B_24), '#skF_4'(A_14, B_24)), A_14) | r1_tarski(A_14, B_24) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.33  tff(c_540, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_11'), '#skF_9'), '#skF_10') | r1_tarski('#skF_10', '#skF_11') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_533, c_30])).
% 2.96/1.33  tff(c_548, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_11'), '#skF_9'), '#skF_10') | r1_tarski('#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_540])).
% 2.96/1.33  tff(c_594, plain, (r1_tarski('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_548])).
% 2.96/1.33  tff(c_599, plain, ('#skF_11'='#skF_10' | ~r1_tarski('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_594, c_2])).
% 2.96/1.33  tff(c_605, plain, (~r1_tarski('#skF_11', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_56, c_599])).
% 2.96/1.33  tff(c_458, plain, (![B_128]: (B_128='#skF_11' | ~r1_tarski(B_128, '#skF_11') | '#skF_4'('#skF_11', B_128)='#skF_9')), inference(resolution, [status(thm)], [c_455, c_2])).
% 2.96/1.33  tff(c_597, plain, ('#skF_11'='#skF_10' | '#skF_4'('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_594, c_458])).
% 2.96/1.33  tff(c_602, plain, ('#skF_4'('#skF_11', '#skF_10')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_56, c_597])).
% 2.96/1.33  tff(c_28, plain, (![A_14, B_24]: (~r2_hidden(k4_tarski('#skF_3'(A_14, B_24), '#skF_4'(A_14, B_24)), B_24) | r1_tarski(A_14, B_24) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.33  tff(c_616, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10') | r1_tarski('#skF_11', '#skF_10') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_602, c_28])).
% 2.96/1.33  tff(c_623, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10') | r1_tarski('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_616])).
% 2.96/1.33  tff(c_624, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_605, c_623])).
% 2.96/1.33  tff(c_613, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_11') | r1_tarski('#skF_11', '#skF_10') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_602, c_30])).
% 2.96/1.33  tff(c_620, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_11') | r1_tarski('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_613])).
% 2.96/1.33  tff(c_621, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_605, c_620])).
% 2.96/1.33  tff(c_664, plain, (r2_hidden('#skF_3'('#skF_11', '#skF_10'), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_621, c_54])).
% 2.96/1.33  tff(c_673, plain, (r2_hidden('#skF_3'('#skF_11', '#skF_10'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_664])).
% 2.96/1.33  tff(c_195, plain, (![D_110]: (k1_funct_1('#skF_10', D_110)='#skF_9' | ~r2_hidden(D_110, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_191, c_8])).
% 2.96/1.33  tff(c_722, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_11', '#skF_10'))='#skF_9'), inference(resolution, [status(thm)], [c_673, c_195])).
% 2.96/1.33  tff(c_50, plain, (![A_71, C_73]: (r2_hidden(k4_tarski(A_71, k1_funct_1(C_73, A_71)), C_73) | ~r2_hidden(A_71, k1_relat_1(C_73)) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.96/1.33  tff(c_726, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_3'('#skF_11', '#skF_10'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_722, c_50])).
% 2.96/1.33  tff(c_742, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_673, c_726])).
% 2.96/1.33  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_742])).
% 2.96/1.33  tff(c_746, plain, (~r1_tarski('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_548])).
% 2.96/1.33  tff(c_745, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_11'), '#skF_9'), '#skF_10')), inference(splitRight, [status(thm)], [c_548])).
% 2.96/1.33  tff(c_759, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_11'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_745, c_54])).
% 2.96/1.33  tff(c_768, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_11'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_759])).
% 2.96/1.33  tff(c_245, plain, (![D_113]: (k1_funct_1('#skF_11', D_113)='#skF_9' | ~r2_hidden(D_113, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_241, c_8])).
% 2.96/1.33  tff(c_815, plain, (k1_funct_1('#skF_11', '#skF_3'('#skF_10', '#skF_11'))='#skF_9'), inference(resolution, [status(thm)], [c_768, c_245])).
% 2.96/1.33  tff(c_851, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_11'), '#skF_9'), '#skF_11') | ~r2_hidden('#skF_3'('#skF_10', '#skF_11'), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_815, c_50])).
% 2.96/1.33  tff(c_867, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_11'), '#skF_9'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_768, c_62, c_851])).
% 2.96/1.33  tff(c_543, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_11'), '#skF_9'), '#skF_11') | r1_tarski('#skF_10', '#skF_11') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_533, c_28])).
% 2.96/1.33  tff(c_550, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_11'), '#skF_9'), '#skF_11') | r1_tarski('#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_543])).
% 2.96/1.33  tff(c_895, plain, (r1_tarski('#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_867, c_550])).
% 2.96/1.33  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_746, c_895])).
% 2.96/1.33  tff(c_898, plain, ('#skF_4'('#skF_10', '#skF_11')!='#skF_9'), inference(splitRight, [status(thm)], [c_491])).
% 2.96/1.33  tff(c_897, plain, ('#skF_4'('#skF_11', '#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_491])).
% 2.96/1.33  tff(c_902, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_11') | r1_tarski('#skF_11', '#skF_10') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_897, c_30])).
% 2.96/1.33  tff(c_909, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_11') | r1_tarski('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_902])).
% 2.96/1.33  tff(c_933, plain, (r1_tarski('#skF_11', '#skF_10')), inference(splitLeft, [status(thm)], [c_909])).
% 2.96/1.33  tff(c_467, plain, (![B_130]: ('#skF_4'('#skF_10', B_130)='#skF_9' | r1_tarski('#skF_10', B_130))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_420])).
% 2.96/1.33  tff(c_470, plain, (![B_130]: (B_130='#skF_10' | ~r1_tarski(B_130, '#skF_10') | '#skF_4'('#skF_10', B_130)='#skF_9')), inference(resolution, [status(thm)], [c_467, c_2])).
% 2.96/1.33  tff(c_936, plain, ('#skF_11'='#skF_10' | '#skF_4'('#skF_10', '#skF_11')='#skF_9'), inference(resolution, [status(thm)], [c_933, c_470])).
% 2.96/1.33  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_898, c_56, c_936])).
% 2.96/1.33  tff(c_944, plain, (~r1_tarski('#skF_11', '#skF_10')), inference(splitRight, [status(thm)], [c_909])).
% 2.96/1.33  tff(c_943, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_11')), inference(splitRight, [status(thm)], [c_909])).
% 2.96/1.33  tff(c_987, plain, (r2_hidden('#skF_3'('#skF_11', '#skF_10'), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_943, c_54])).
% 2.96/1.33  tff(c_996, plain, (r2_hidden('#skF_3'('#skF_11', '#skF_10'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_987])).
% 2.96/1.33  tff(c_1045, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_11', '#skF_10'))='#skF_9'), inference(resolution, [status(thm)], [c_996, c_195])).
% 2.96/1.33  tff(c_1058, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_3'('#skF_11', '#skF_10'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_50])).
% 2.96/1.33  tff(c_1074, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_996, c_1058])).
% 2.96/1.33  tff(c_905, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10') | r1_tarski('#skF_11', '#skF_10') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_897, c_28])).
% 2.96/1.33  tff(c_911, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_10'), '#skF_9'), '#skF_10') | r1_tarski('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_905])).
% 2.96/1.33  tff(c_1102, plain, (r1_tarski('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_911])).
% 2.96/1.33  tff(c_1103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_944, c_1102])).
% 2.96/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.33  
% 2.96/1.33  Inference rules
% 2.96/1.33  ----------------------
% 2.96/1.33  #Ref     : 0
% 2.96/1.33  #Sup     : 212
% 2.96/1.33  #Fact    : 0
% 2.96/1.33  #Define  : 0
% 2.96/1.33  #Split   : 3
% 2.96/1.33  #Chain   : 0
% 2.96/1.33  #Close   : 0
% 2.96/1.33  
% 2.96/1.33  Ordering : KBO
% 2.96/1.33  
% 2.96/1.33  Simplification rules
% 2.96/1.33  ----------------------
% 2.96/1.33  #Subsume      : 5
% 2.96/1.33  #Demod        : 258
% 2.96/1.33  #Tautology    : 115
% 2.96/1.33  #SimpNegUnit  : 27
% 2.96/1.33  #BackRed      : 0
% 2.96/1.33  
% 2.96/1.33  #Partial instantiations: 0
% 2.96/1.33  #Strategies tried      : 1
% 2.96/1.33  
% 2.96/1.33  Timing (in seconds)
% 2.96/1.33  ----------------------
% 2.96/1.33  Preprocessing        : 0.34
% 2.96/1.33  Parsing              : 0.17
% 2.96/1.33  CNF conversion       : 0.03
% 2.96/1.33  Main loop            : 0.38
% 2.96/1.33  Inferencing          : 0.13
% 2.96/1.33  Reduction            : 0.13
% 2.96/1.33  Demodulation         : 0.09
% 2.96/1.33  BG Simplification    : 0.03
% 2.96/1.33  Subsumption          : 0.07
% 2.96/1.33  Abstraction          : 0.02
% 2.96/1.33  MUC search           : 0.00
% 2.96/1.33  Cooper               : 0.00
% 2.96/1.33  Total                : 0.76
% 2.96/1.33  Index Insertion      : 0.00
% 2.96/1.33  Index Deletion       : 0.00
% 2.96/1.33  Index Matching       : 0.00
% 2.96/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
