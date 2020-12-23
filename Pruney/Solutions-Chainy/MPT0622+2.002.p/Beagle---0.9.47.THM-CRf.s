%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:05 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  136 (2585 expanded)
%              Number of leaves         :   29 ( 935 expanded)
%              Depth                    :   26
%              Number of atoms          :  250 (9628 expanded)
%              Number of equality atoms :   56 (3144 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_174,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(k4_tarski('#skF_3'(A_75,B_76),'#skF_4'(A_75,B_76)),A_75)
      | r1_tarski(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [C_39,A_37,B_38] :
      ( k1_funct_1(C_39,A_37) = B_38
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_401,plain,(
    ! [A_96,B_97] :
      ( k1_funct_1(A_96,'#skF_3'(A_96,B_97)) = '#skF_4'(A_96,B_97)
      | ~ v1_funct_1(A_96)
      | r1_tarski(A_96,B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_174,c_38])).

tff(c_48,plain,(
    k1_relat_1('#skF_7') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    ! [A_37,C_39,B_38] :
      ( r2_hidden(A_37,k1_relat_1(C_39))
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_214,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_3'(A_79,B_80),k1_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | r1_tarski(A_79,B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_174,c_40])).

tff(c_225,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_3'('#skF_7',B_80),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | r1_tarski('#skF_7',B_80)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_214])).

tff(c_234,plain,(
    ! [B_81] :
      ( r2_hidden('#skF_3'('#skF_7',B_81),k1_relat_1('#skF_6'))
      | r1_tarski('#skF_7',B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_225])).

tff(c_44,plain,(
    k2_relat_1('#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_147,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(k1_funct_1(B_71,A_72),k2_relat_1(B_71))
      | ~ r2_hidden(A_72,k1_relat_1(B_71))
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    ! [A_72] :
      ( r2_hidden(k1_funct_1('#skF_7',A_72),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_72,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_147])).

tff(c_193,plain,(
    ! [A_77] :
      ( r2_hidden(k1_funct_1('#skF_7',A_77),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_77,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_153])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_197,plain,(
    ! [A_77] :
      ( k1_funct_1('#skF_7',A_77) = '#skF_5'
      | ~ r2_hidden(A_77,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_193,c_8])).

tff(c_241,plain,(
    ! [B_81] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_7',B_81)) = '#skF_5'
      | r1_tarski('#skF_7',B_81) ) ),
    inference(resolution,[status(thm)],[c_234,c_197])).

tff(c_411,plain,(
    ! [B_97] :
      ( '#skF_4'('#skF_7',B_97) = '#skF_5'
      | r1_tarski('#skF_7',B_97)
      | ~ v1_funct_1('#skF_7')
      | r1_tarski('#skF_7',B_97)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_241])).

tff(c_438,plain,(
    ! [B_97] :
      ( '#skF_4'('#skF_7',B_97) = '#skF_5'
      | r1_tarski('#skF_7',B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_411])).

tff(c_56,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    k2_relat_1('#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_150,plain,(
    ! [A_72] :
      ( r2_hidden(k1_funct_1('#skF_6',A_72),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_72,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_147])).

tff(c_158,plain,(
    ! [A_73] :
      ( r2_hidden(k1_funct_1('#skF_6',A_73),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_73,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_150])).

tff(c_162,plain,(
    ! [A_73] :
      ( k1_funct_1('#skF_6',A_73) = '#skF_5'
      | ~ r2_hidden(A_73,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_158,c_8])).

tff(c_222,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_80)) = '#skF_5'
      | ~ v1_funct_1('#skF_6')
      | r1_tarski('#skF_6',B_80)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_214,c_162])).

tff(c_231,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_80)) = '#skF_5'
      | r1_tarski('#skF_6',B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_222])).

tff(c_435,plain,(
    ! [B_80] :
      ( '#skF_4'('#skF_6',B_80) = '#skF_5'
      | ~ v1_funct_1('#skF_6')
      | r1_tarski('#skF_6',B_80)
      | ~ v1_relat_1('#skF_6')
      | r1_tarski('#skF_6',B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_401])).

tff(c_459,plain,(
    ! [B_100] :
      ( '#skF_4'('#skF_6',B_100) = '#skF_5'
      | r1_tarski('#skF_6',B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_435])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_469,plain,(
    ! [B_104] :
      ( B_104 = '#skF_6'
      | ~ r1_tarski(B_104,'#skF_6')
      | '#skF_4'('#skF_6',B_104) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_459,c_2])).

tff(c_477,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_4'('#skF_6','#skF_7') = '#skF_5'
    | '#skF_4'('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_438,c_469])).

tff(c_486,plain,
    ( '#skF_4'('#skF_6','#skF_7') = '#skF_5'
    | '#skF_4'('#skF_7','#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_477])).

tff(c_489,plain,(
    '#skF_4'('#skF_7','#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_30,plain,(
    ! [A_18,B_28] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_18,B_28),'#skF_4'(A_18,B_28)),B_28)
      | r1_tarski(A_18,B_28)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_496,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_30])).

tff(c_504,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_496])).

tff(c_508,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_32,plain,(
    ! [A_18,B_28] :
      ( r2_hidden(k4_tarski('#skF_3'(A_18,B_28),'#skF_4'(A_18,B_28)),A_18)
      | r1_tarski(A_18,B_28)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_499,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_32])).

tff(c_506,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_499])).

tff(c_529,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_534,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_529,c_2])).

tff(c_540,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_534])).

tff(c_462,plain,(
    ! [B_100] :
      ( B_100 = '#skF_6'
      | ~ r1_tarski(B_100,'#skF_6')
      | '#skF_4'('#skF_6',B_100) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_459,c_2])).

tff(c_532,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_4'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_529,c_462])).

tff(c_537,plain,(
    '#skF_4'('#skF_6','#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_532])).

tff(c_555,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_30])).

tff(c_562,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_555])).

tff(c_563,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_540,c_562])).

tff(c_558,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_32])).

tff(c_565,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_558])).

tff(c_566,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_540,c_565])).

tff(c_576,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_566,c_40])).

tff(c_585,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_576])).

tff(c_632,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_6','#skF_7')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_585,c_197])).

tff(c_36,plain,(
    ! [A_37,C_39] :
      ( r2_hidden(k4_tarski(A_37,k1_funct_1(C_39,A_37)),C_39)
      | ~ r2_hidden(A_37,k1_relat_1(C_39))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_638,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_36])).

tff(c_654,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_585,c_48,c_638])).

tff(c_656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_654])).

tff(c_657,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_671,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_657,c_40])).

tff(c_680,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_671])).

tff(c_736,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_7','#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_680,c_162])).

tff(c_740,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_36])).

tff(c_756,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),'#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_680,c_740])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_756])).

tff(c_759,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_766,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_759,c_2])).

tff(c_772,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_766])).

tff(c_764,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_4'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_759,c_462])).

tff(c_769,plain,(
    '#skF_4'('#skF_6','#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_764])).

tff(c_781,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_30])).

tff(c_788,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_781])).

tff(c_789,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_788])).

tff(c_784,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_32])).

tff(c_791,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_784])).

tff(c_792,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_791])).

tff(c_863,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_792,c_40])).

tff(c_872,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_863])).

tff(c_958,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_6','#skF_7')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_872,c_197])).

tff(c_964,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_36])).

tff(c_980,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_872,c_48,c_964])).

tff(c_1022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_789,c_980])).

tff(c_1024,plain,(
    '#skF_4'('#skF_7','#skF_6') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_1023,plain,(
    '#skF_4'('#skF_6','#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_1028,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_30])).

tff(c_1035,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1028])).

tff(c_1059,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1035])).

tff(c_1031,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_32])).

tff(c_1037,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1031])).

tff(c_1060,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1037])).

tff(c_455,plain,(
    ! [B_99] :
      ( '#skF_4'('#skF_7',B_99) = '#skF_5'
      | r1_tarski('#skF_7',B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_411])).

tff(c_458,plain,(
    ! [B_99] :
      ( B_99 = '#skF_7'
      | ~ r1_tarski(B_99,'#skF_7')
      | '#skF_4'('#skF_7',B_99) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_1063,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_4'('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1060,c_458])).

tff(c_1069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1024,c_42,c_1063])).

tff(c_1070,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1037])).

tff(c_1091,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1070,c_40])).

tff(c_1100,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1091])).

tff(c_1161,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_6','#skF_7')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1100,c_197])).

tff(c_1167,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_36])).

tff(c_1183,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_7'),'#skF_5'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1100,c_48,c_1167])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_1183])).

tff(c_1186,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1035])).

tff(c_1190,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_4'('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1186,c_458])).

tff(c_1196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1024,c_42,c_1190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:36:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.50  
% 3.02/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.50  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.02/1.50  
% 3.02/1.50  %Foreground sorts:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Background operators:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Foreground operators:
% 3.02/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.02/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.02/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.02/1.50  
% 3.39/1.53  tff(f_92, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 3.39/1.53  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 3.39/1.53  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.39/1.53  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.39/1.53  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.39/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.53  tff(c_42, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_52, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_174, plain, (![A_75, B_76]: (r2_hidden(k4_tarski('#skF_3'(A_75, B_76), '#skF_4'(A_75, B_76)), A_75) | r1_tarski(A_75, B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.39/1.53  tff(c_38, plain, (![C_39, A_37, B_38]: (k1_funct_1(C_39, A_37)=B_38 | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.53  tff(c_401, plain, (![A_96, B_97]: (k1_funct_1(A_96, '#skF_3'(A_96, B_97))='#skF_4'(A_96, B_97) | ~v1_funct_1(A_96) | r1_tarski(A_96, B_97) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_174, c_38])).
% 3.39/1.53  tff(c_48, plain, (k1_relat_1('#skF_7')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_40, plain, (![A_37, C_39, B_38]: (r2_hidden(A_37, k1_relat_1(C_39)) | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.53  tff(c_214, plain, (![A_79, B_80]: (r2_hidden('#skF_3'(A_79, B_80), k1_relat_1(A_79)) | ~v1_funct_1(A_79) | r1_tarski(A_79, B_80) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_174, c_40])).
% 3.39/1.53  tff(c_225, plain, (![B_80]: (r2_hidden('#skF_3'('#skF_7', B_80), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_7') | r1_tarski('#skF_7', B_80) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_214])).
% 3.39/1.53  tff(c_234, plain, (![B_81]: (r2_hidden('#skF_3'('#skF_7', B_81), k1_relat_1('#skF_6')) | r1_tarski('#skF_7', B_81))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_225])).
% 3.39/1.53  tff(c_44, plain, (k2_relat_1('#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_147, plain, (![B_71, A_72]: (r2_hidden(k1_funct_1(B_71, A_72), k2_relat_1(B_71)) | ~r2_hidden(A_72, k1_relat_1(B_71)) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.53  tff(c_153, plain, (![A_72]: (r2_hidden(k1_funct_1('#skF_7', A_72), k1_tarski('#skF_5')) | ~r2_hidden(A_72, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_147])).
% 3.39/1.53  tff(c_193, plain, (![A_77]: (r2_hidden(k1_funct_1('#skF_7', A_77), k1_tarski('#skF_5')) | ~r2_hidden(A_77, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_153])).
% 3.39/1.53  tff(c_8, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.53  tff(c_197, plain, (![A_77]: (k1_funct_1('#skF_7', A_77)='#skF_5' | ~r2_hidden(A_77, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_193, c_8])).
% 3.39/1.53  tff(c_241, plain, (![B_81]: (k1_funct_1('#skF_7', '#skF_3'('#skF_7', B_81))='#skF_5' | r1_tarski('#skF_7', B_81))), inference(resolution, [status(thm)], [c_234, c_197])).
% 3.39/1.53  tff(c_411, plain, (![B_97]: ('#skF_4'('#skF_7', B_97)='#skF_5' | r1_tarski('#skF_7', B_97) | ~v1_funct_1('#skF_7') | r1_tarski('#skF_7', B_97) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_401, c_241])).
% 3.39/1.53  tff(c_438, plain, (![B_97]: ('#skF_4'('#skF_7', B_97)='#skF_5' | r1_tarski('#skF_7', B_97))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_411])).
% 3.39/1.53  tff(c_56, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_46, plain, (k2_relat_1('#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.53  tff(c_150, plain, (![A_72]: (r2_hidden(k1_funct_1('#skF_6', A_72), k1_tarski('#skF_5')) | ~r2_hidden(A_72, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_147])).
% 3.39/1.53  tff(c_158, plain, (![A_73]: (r2_hidden(k1_funct_1('#skF_6', A_73), k1_tarski('#skF_5')) | ~r2_hidden(A_73, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_150])).
% 3.39/1.53  tff(c_162, plain, (![A_73]: (k1_funct_1('#skF_6', A_73)='#skF_5' | ~r2_hidden(A_73, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_158, c_8])).
% 3.39/1.53  tff(c_222, plain, (![B_80]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_80))='#skF_5' | ~v1_funct_1('#skF_6') | r1_tarski('#skF_6', B_80) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_214, c_162])).
% 3.39/1.53  tff(c_231, plain, (![B_80]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_80))='#skF_5' | r1_tarski('#skF_6', B_80))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_222])).
% 3.39/1.53  tff(c_435, plain, (![B_80]: ('#skF_4'('#skF_6', B_80)='#skF_5' | ~v1_funct_1('#skF_6') | r1_tarski('#skF_6', B_80) | ~v1_relat_1('#skF_6') | r1_tarski('#skF_6', B_80))), inference(superposition, [status(thm), theory('equality')], [c_231, c_401])).
% 3.39/1.53  tff(c_459, plain, (![B_100]: ('#skF_4'('#skF_6', B_100)='#skF_5' | r1_tarski('#skF_6', B_100))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_435])).
% 3.39/1.53  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.53  tff(c_469, plain, (![B_104]: (B_104='#skF_6' | ~r1_tarski(B_104, '#skF_6') | '#skF_4'('#skF_6', B_104)='#skF_5')), inference(resolution, [status(thm)], [c_459, c_2])).
% 3.39/1.53  tff(c_477, plain, ('#skF_7'='#skF_6' | '#skF_4'('#skF_6', '#skF_7')='#skF_5' | '#skF_4'('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_438, c_469])).
% 3.39/1.53  tff(c_486, plain, ('#skF_4'('#skF_6', '#skF_7')='#skF_5' | '#skF_4'('#skF_7', '#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_42, c_477])).
% 3.39/1.53  tff(c_489, plain, ('#skF_4'('#skF_7', '#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_486])).
% 3.39/1.53  tff(c_30, plain, (![A_18, B_28]: (~r2_hidden(k4_tarski('#skF_3'(A_18, B_28), '#skF_4'(A_18, B_28)), B_28) | r1_tarski(A_18, B_28) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.39/1.53  tff(c_496, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_6') | r1_tarski('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_489, c_30])).
% 3.39/1.53  tff(c_504, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_6') | r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_496])).
% 3.39/1.53  tff(c_508, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_504])).
% 3.39/1.53  tff(c_32, plain, (![A_18, B_28]: (r2_hidden(k4_tarski('#skF_3'(A_18, B_28), '#skF_4'(A_18, B_28)), A_18) | r1_tarski(A_18, B_28) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.39/1.53  tff(c_499, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_7') | r1_tarski('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_489, c_32])).
% 3.39/1.53  tff(c_506, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_7') | r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_499])).
% 3.39/1.53  tff(c_529, plain, (r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_506])).
% 3.39/1.53  tff(c_534, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_529, c_2])).
% 3.39/1.53  tff(c_540, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_42, c_534])).
% 3.39/1.53  tff(c_462, plain, (![B_100]: (B_100='#skF_6' | ~r1_tarski(B_100, '#skF_6') | '#skF_4'('#skF_6', B_100)='#skF_5')), inference(resolution, [status(thm)], [c_459, c_2])).
% 3.39/1.53  tff(c_532, plain, ('#skF_7'='#skF_6' | '#skF_4'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_529, c_462])).
% 3.39/1.53  tff(c_537, plain, ('#skF_4'('#skF_6', '#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_42, c_532])).
% 3.39/1.53  tff(c_555, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_537, c_30])).
% 3.39/1.53  tff(c_562, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_555])).
% 3.39/1.53  tff(c_563, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_540, c_562])).
% 3.39/1.53  tff(c_558, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6') | r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_537, c_32])).
% 3.39/1.53  tff(c_565, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6') | r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_558])).
% 3.39/1.53  tff(c_566, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_540, c_565])).
% 3.39/1.53  tff(c_576, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_566, c_40])).
% 3.39/1.53  tff(c_585, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_576])).
% 3.39/1.53  tff(c_632, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_6', '#skF_7'))='#skF_5'), inference(resolution, [status(thm)], [c_585, c_197])).
% 3.39/1.53  tff(c_36, plain, (![A_37, C_39]: (r2_hidden(k4_tarski(A_37, k1_funct_1(C_39, A_37)), C_39) | ~r2_hidden(A_37, k1_relat_1(C_39)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.53  tff(c_638, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | ~r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_632, c_36])).
% 3.39/1.53  tff(c_654, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_585, c_48, c_638])).
% 3.39/1.53  tff(c_656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_563, c_654])).
% 3.39/1.53  tff(c_657, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_506])).
% 3.39/1.53  tff(c_671, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_657, c_40])).
% 3.39/1.53  tff(c_680, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_671])).
% 3.39/1.53  tff(c_736, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_7', '#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_680, c_162])).
% 3.39/1.53  tff(c_740, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_6') | ~r2_hidden('#skF_3'('#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_736, c_36])).
% 3.39/1.53  tff(c_756, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_680, c_740])).
% 3.39/1.53  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_756])).
% 3.39/1.53  tff(c_759, plain, (r1_tarski('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_504])).
% 3.39/1.53  tff(c_766, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_759, c_2])).
% 3.39/1.53  tff(c_772, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_42, c_766])).
% 3.39/1.53  tff(c_764, plain, ('#skF_7'='#skF_6' | '#skF_4'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_759, c_462])).
% 3.39/1.53  tff(c_769, plain, ('#skF_4'('#skF_6', '#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_42, c_764])).
% 3.39/1.53  tff(c_781, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_769, c_30])).
% 3.39/1.53  tff(c_788, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_781])).
% 3.39/1.53  tff(c_789, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_772, c_788])).
% 3.39/1.53  tff(c_784, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6') | r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_769, c_32])).
% 3.39/1.53  tff(c_791, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6') | r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_784])).
% 3.39/1.53  tff(c_792, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_772, c_791])).
% 3.39/1.53  tff(c_863, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_792, c_40])).
% 3.39/1.53  tff(c_872, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_863])).
% 3.39/1.53  tff(c_958, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_6', '#skF_7'))='#skF_5'), inference(resolution, [status(thm)], [c_872, c_197])).
% 3.39/1.53  tff(c_964, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | ~r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_958, c_36])).
% 3.39/1.53  tff(c_980, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_872, c_48, c_964])).
% 3.39/1.53  tff(c_1022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_789, c_980])).
% 3.39/1.53  tff(c_1024, plain, ('#skF_4'('#skF_7', '#skF_6')!='#skF_5'), inference(splitRight, [status(thm)], [c_486])).
% 3.39/1.53  tff(c_1023, plain, ('#skF_4'('#skF_6', '#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_486])).
% 3.39/1.53  tff(c_1028, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1023, c_30])).
% 3.39/1.53  tff(c_1035, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1028])).
% 3.39/1.53  tff(c_1059, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1035])).
% 3.39/1.53  tff(c_1031, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6') | r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1023, c_32])).
% 3.39/1.53  tff(c_1037, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6') | r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1031])).
% 3.39/1.53  tff(c_1060, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_1037])).
% 3.39/1.53  tff(c_455, plain, (![B_99]: ('#skF_4'('#skF_7', B_99)='#skF_5' | r1_tarski('#skF_7', B_99))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_411])).
% 3.39/1.53  tff(c_458, plain, (![B_99]: (B_99='#skF_7' | ~r1_tarski(B_99, '#skF_7') | '#skF_4'('#skF_7', B_99)='#skF_5')), inference(resolution, [status(thm)], [c_455, c_2])).
% 3.39/1.53  tff(c_1063, plain, ('#skF_7'='#skF_6' | '#skF_4'('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1060, c_458])).
% 3.39/1.53  tff(c_1069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1024, c_42, c_1063])).
% 3.39/1.53  tff(c_1070, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_1037])).
% 3.39/1.53  tff(c_1091, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1070, c_40])).
% 3.39/1.53  tff(c_1100, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1091])).
% 3.39/1.53  tff(c_1161, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_6', '#skF_7'))='#skF_5'), inference(resolution, [status(thm)], [c_1100, c_197])).
% 3.39/1.53  tff(c_1167, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7') | ~r2_hidden('#skF_3'('#skF_6', '#skF_7'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1161, c_36])).
% 3.39/1.53  tff(c_1183, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_7'), '#skF_5'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1100, c_48, c_1167])).
% 3.39/1.53  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1059, c_1183])).
% 3.39/1.53  tff(c_1186, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_1035])).
% 3.39/1.53  tff(c_1190, plain, ('#skF_7'='#skF_6' | '#skF_4'('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1186, c_458])).
% 3.39/1.53  tff(c_1196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1024, c_42, c_1190])).
% 3.39/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.53  
% 3.39/1.53  Inference rules
% 3.39/1.53  ----------------------
% 3.39/1.53  #Ref     : 0
% 3.39/1.53  #Sup     : 241
% 3.39/1.53  #Fact    : 0
% 3.39/1.53  #Define  : 0
% 3.39/1.53  #Split   : 6
% 3.39/1.53  #Chain   : 0
% 3.39/1.53  #Close   : 0
% 3.39/1.53  
% 3.39/1.53  Ordering : KBO
% 3.39/1.53  
% 3.39/1.53  Simplification rules
% 3.39/1.53  ----------------------
% 3.39/1.53  #Subsume      : 5
% 3.39/1.53  #Demod        : 236
% 3.39/1.53  #Tautology    : 137
% 3.39/1.53  #SimpNegUnit  : 36
% 3.39/1.53  #BackRed      : 0
% 3.39/1.53  
% 3.39/1.53  #Partial instantiations: 0
% 3.39/1.53  #Strategies tried      : 1
% 3.39/1.53  
% 3.39/1.53  Timing (in seconds)
% 3.39/1.53  ----------------------
% 3.39/1.53  Preprocessing        : 0.32
% 3.39/1.53  Parsing              : 0.16
% 3.39/1.53  CNF conversion       : 0.02
% 3.39/1.53  Main loop            : 0.42
% 3.39/1.53  Inferencing          : 0.15
% 3.39/1.53  Reduction            : 0.14
% 3.39/1.53  Demodulation         : 0.10
% 3.39/1.53  BG Simplification    : 0.02
% 3.39/1.53  Subsumption          : 0.07
% 3.39/1.53  Abstraction          : 0.02
% 3.39/1.53  MUC search           : 0.00
% 3.39/1.53  Cooper               : 0.00
% 3.39/1.53  Total                : 0.79
% 3.39/1.53  Index Insertion      : 0.00
% 3.39/1.53  Index Deletion       : 0.00
% 3.39/1.53  Index Matching       : 0.00
% 3.39/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
