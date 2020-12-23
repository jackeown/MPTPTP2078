%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0541+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:27 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 137 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 355 expanded)
%              Number of equality atoms :    2 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(A,k9_relat_1(C,B))
        <=> ? [D] :
              ( r2_hidden(D,k1_relat_1(C))
              & r2_hidden(k4_tarski(D,A),C)
              & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_40,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | r2_hidden('#skF_12','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    r2_hidden('#skF_12','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | r2_hidden(k4_tarski('#skF_12','#skF_9'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_9'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_66,plain,(
    ! [D_75,A_76,B_77,E_78] :
      ( r2_hidden(D_75,k9_relat_1(A_76,B_77))
      | ~ r2_hidden(E_78,B_77)
      | ~ r2_hidden(k4_tarski(E_78,D_75),A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [D_79,A_80] :
      ( r2_hidden(D_79,k9_relat_1(A_80,'#skF_10'))
      | ~ r2_hidden(k4_tarski('#skF_12',D_79),A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_49,c_66])).

tff(c_89,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_52,c_82])).

tff(c_93,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_89])).

tff(c_34,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_64,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10')) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    ! [D_94] :
      ( ~ r2_hidden(D_94,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_94,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_94,k1_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_34])).

tff(c_172,plain,
    ( ~ r2_hidden('#skF_12','#skF_10')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_52,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_49,c_172])).

tff(c_177,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_303,plain,(
    ! [A_130,B_131,D_132] :
      ( r2_hidden(k4_tarski('#skF_4'(A_130,B_131,k9_relat_1(A_130,B_131),D_132),D_132),A_130)
      | ~ r2_hidden(D_132,k9_relat_1(A_130,B_131))
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k1_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(C_58,D_61),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_317,plain,(
    ! [A_130,B_131,D_132] :
      ( r2_hidden('#skF_4'(A_130,B_131,k9_relat_1(A_130,B_131),D_132),k1_relat_1(A_130))
      | ~ r2_hidden(D_132,k9_relat_1(A_130,B_131))
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_303,c_22])).

tff(c_178,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_9'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_64,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_11'))
      | r2_hidden(k4_tarski('#skF_12','#skF_9'),'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_279,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_64,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_42])).

tff(c_307,plain,(
    ! [B_131] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_131,k9_relat_1('#skF_11',B_131),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_4'('#skF_11',B_131,k9_relat_1('#skF_11',B_131),'#skF_9'),k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_131))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_303,c_279])).

tff(c_586,plain,(
    ! [B_188] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_188,k9_relat_1('#skF_11',B_188),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_4'('#skF_11',B_188,k9_relat_1('#skF_11',B_188),'#skF_9'),k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_188)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_307])).

tff(c_590,plain,(
    ! [B_131] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_131,k9_relat_1('#skF_11',B_131),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_131))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_317,c_586])).

tff(c_601,plain,(
    ! [B_189] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_189,k9_relat_1('#skF_11',B_189),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_189)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_590])).

tff(c_605,plain,
    ( ~ r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_601])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_177,c_605])).

tff(c_610,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_692,plain,(
    ! [A_220,B_221,D_222] :
      ( r2_hidden(k4_tarski('#skF_4'(A_220,B_221,k9_relat_1(A_220,B_221),D_222),D_222),A_220)
      | ~ r2_hidden(D_222,k9_relat_1(A_220,B_221))
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_706,plain,(
    ! [A_220,B_221,D_222] :
      ( r2_hidden('#skF_4'(A_220,B_221,k9_relat_1(A_220,B_221),D_222),k1_relat_1(A_220))
      | ~ r2_hidden(D_222,k9_relat_1(A_220,B_221))
      | ~ v1_relat_1(A_220) ) ),
    inference(resolution,[status(thm)],[c_692,c_22])).

tff(c_611,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_64,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_11'))
      | r2_hidden('#skF_12',k1_relat_1('#skF_11')) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_667,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_64,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_46])).

tff(c_696,plain,(
    ! [B_221] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_221,k9_relat_1('#skF_11',B_221),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_4'('#skF_11',B_221,k9_relat_1('#skF_11',B_221),'#skF_9'),k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_221))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_692,c_667])).

tff(c_856,plain,(
    ! [B_275] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_275,k9_relat_1('#skF_11',B_275),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_4'('#skF_11',B_275,k9_relat_1('#skF_11',B_275),'#skF_9'),k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_275)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_696])).

tff(c_860,plain,(
    ! [B_221] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_221,k9_relat_1('#skF_11',B_221),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_221))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_706,c_856])).

tff(c_871,plain,(
    ! [B_276] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_276,k9_relat_1('#skF_11',B_276),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_276)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_860])).

tff(c_875,plain,
    ( ~ r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_871])).

tff(c_879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_610,c_875])).

tff(c_880,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_955,plain,(
    ! [A_308,B_309,D_310] :
      ( r2_hidden(k4_tarski('#skF_4'(A_308,B_309,k9_relat_1(A_308,B_309),D_310),D_310),A_308)
      | ~ r2_hidden(D_310,k9_relat_1(A_308,B_309))
      | ~ v1_relat_1(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_972,plain,(
    ! [A_308,B_309,D_310] :
      ( r2_hidden('#skF_4'(A_308,B_309,k9_relat_1(A_308,B_309),D_310),k1_relat_1(A_308))
      | ~ r2_hidden(D_310,k9_relat_1(A_308,B_309))
      | ~ v1_relat_1(A_308) ) ),
    inference(resolution,[status(thm)],[c_955,c_22])).

tff(c_881,plain,(
    ~ r2_hidden('#skF_12','#skF_10') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_64,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_11'))
      | r2_hidden('#skF_12','#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_891,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_64,'#skF_9'),'#skF_11')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_881,c_38])).

tff(c_963,plain,(
    ! [B_309] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_309,k9_relat_1('#skF_11',B_309),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_4'('#skF_11',B_309,k9_relat_1('#skF_11',B_309),'#skF_9'),k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_309))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_955,c_891])).

tff(c_1037,plain,(
    ! [B_335] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_335,k9_relat_1('#skF_11',B_335),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_4'('#skF_11',B_335,k9_relat_1('#skF_11',B_335),'#skF_9'),k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_335)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_963])).

tff(c_1041,plain,(
    ! [B_309] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_309,k9_relat_1('#skF_11',B_309),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_309))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_972,c_1037])).

tff(c_1052,plain,(
    ! [B_336] :
      ( ~ r2_hidden('#skF_4'('#skF_11',B_336,k9_relat_1('#skF_11',B_336),'#skF_9'),'#skF_10')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_11',B_336)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1041])).

tff(c_1056,plain,
    ( ~ r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_1052])).

tff(c_1060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_880,c_1056])).

%------------------------------------------------------------------------------
