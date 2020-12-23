%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:32 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.39s
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(A,k9_relat_1(C,B))
        <=> ? [D] :
              ( r2_hidden(D,k1_relat_1(C))
              & r2_hidden(k4_tarski(D,A),C)
              & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_40,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | r2_hidden('#skF_12','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_49,plain,(
    r2_hidden('#skF_12','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_11','#skF_10'))
    | r2_hidden(k4_tarski('#skF_12','#skF_9'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_9'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_66,plain,(
    ! [D_75,A_76,B_77,E_78] :
      ( r2_hidden(D_75,k9_relat_1(A_76,B_77))
      | ~ r2_hidden(E_78,B_77)
      | ~ r2_hidden(k4_tarski(E_78,D_75),A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

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
    inference(cnfTransformation,[status(thm)],[f_58])).

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
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_303,plain,(
    ! [A_130,B_131,D_132] :
      ( r2_hidden(k4_tarski('#skF_4'(A_130,B_131,k9_relat_1(A_130,B_131),D_132),D_132),A_130)
      | ~ r2_hidden(D_132,k9_relat_1(A_130,B_131))
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k1_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(C_58,D_61),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

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
    inference(cnfTransformation,[status(thm)],[f_58])).

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
    inference(cnfTransformation,[status(thm)],[f_38])).

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
    inference(cnfTransformation,[status(thm)],[f_58])).

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
    inference(cnfTransformation,[status(thm)],[f_38])).

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
    inference(cnfTransformation,[status(thm)],[f_58])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.53  
% 3.12/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.53  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12
% 3.39/1.53  
% 3.39/1.53  %Foreground sorts:
% 3.39/1.53  
% 3.39/1.53  
% 3.39/1.53  %Background operators:
% 3.39/1.53  
% 3.39/1.53  
% 3.39/1.53  %Foreground operators:
% 3.39/1.53  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.39/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.53  tff('#skF_11', type, '#skF_11': $i).
% 3.39/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.39/1.53  tff('#skF_10', type, '#skF_10': $i).
% 3.39/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.39/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.39/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.39/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.53  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.39/1.53  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.39/1.53  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.39/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.53  tff('#skF_12', type, '#skF_12': $i).
% 3.39/1.53  
% 3.39/1.55  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.39/1.55  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 3.39/1.55  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.39/1.55  tff(c_32, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_48, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')) | r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_50, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.39/1.55  tff(c_40, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')) | r2_hidden('#skF_12', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_49, plain, (r2_hidden('#skF_12', '#skF_10')), inference(splitLeft, [status(thm)], [c_40])).
% 3.39/1.55  tff(c_44, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')) | r2_hidden(k4_tarski('#skF_12', '#skF_9'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_52, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_9'), '#skF_11')), inference(splitLeft, [status(thm)], [c_44])).
% 3.39/1.55  tff(c_66, plain, (![D_75, A_76, B_77, E_78]: (r2_hidden(D_75, k9_relat_1(A_76, B_77)) | ~r2_hidden(E_78, B_77) | ~r2_hidden(k4_tarski(E_78, D_75), A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.55  tff(c_82, plain, (![D_79, A_80]: (r2_hidden(D_79, k9_relat_1(A_80, '#skF_10')) | ~r2_hidden(k4_tarski('#skF_12', D_79), A_80) | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_49, c_66])).
% 3.39/1.55  tff(c_89, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_52, c_82])).
% 3.39/1.55  tff(c_93, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_89])).
% 3.39/1.55  tff(c_34, plain, (![D_64]: (~r2_hidden(D_64, '#skF_10') | ~r2_hidden(k4_tarski(D_64, '#skF_9'), '#skF_11') | ~r2_hidden(D_64, k1_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_169, plain, (![D_94]: (~r2_hidden(D_94, '#skF_10') | ~r2_hidden(k4_tarski(D_94, '#skF_9'), '#skF_11') | ~r2_hidden(D_94, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_34])).
% 3.39/1.55  tff(c_172, plain, (~r2_hidden('#skF_12', '#skF_10') | ~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_52, c_169])).
% 3.39/1.55  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_49, c_172])).
% 3.39/1.55  tff(c_177, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_44])).
% 3.39/1.55  tff(c_4, plain, (![A_1, B_24, D_39]: (r2_hidden('#skF_4'(A_1, B_24, k9_relat_1(A_1, B_24), D_39), B_24) | ~r2_hidden(D_39, k9_relat_1(A_1, B_24)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.55  tff(c_303, plain, (![A_130, B_131, D_132]: (r2_hidden(k4_tarski('#skF_4'(A_130, B_131, k9_relat_1(A_130, B_131), D_132), D_132), A_130) | ~r2_hidden(D_132, k9_relat_1(A_130, B_131)) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.55  tff(c_22, plain, (![C_58, A_43, D_61]: (r2_hidden(C_58, k1_relat_1(A_43)) | ~r2_hidden(k4_tarski(C_58, D_61), A_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.55  tff(c_317, plain, (![A_130, B_131, D_132]: (r2_hidden('#skF_4'(A_130, B_131, k9_relat_1(A_130, B_131), D_132), k1_relat_1(A_130)) | ~r2_hidden(D_132, k9_relat_1(A_130, B_131)) | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_303, c_22])).
% 3.39/1.55  tff(c_178, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_9'), '#skF_11')), inference(splitRight, [status(thm)], [c_44])).
% 3.39/1.55  tff(c_42, plain, (![D_64]: (~r2_hidden(D_64, '#skF_10') | ~r2_hidden(k4_tarski(D_64, '#skF_9'), '#skF_11') | ~r2_hidden(D_64, k1_relat_1('#skF_11')) | r2_hidden(k4_tarski('#skF_12', '#skF_9'), '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_279, plain, (![D_64]: (~r2_hidden(D_64, '#skF_10') | ~r2_hidden(k4_tarski(D_64, '#skF_9'), '#skF_11') | ~r2_hidden(D_64, k1_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_178, c_42])).
% 3.39/1.55  tff(c_307, plain, (![B_131]: (~r2_hidden('#skF_4'('#skF_11', B_131, k9_relat_1('#skF_11', B_131), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_4'('#skF_11', B_131, k9_relat_1('#skF_11', B_131), '#skF_9'), k1_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_131)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_303, c_279])).
% 3.39/1.55  tff(c_586, plain, (![B_188]: (~r2_hidden('#skF_4'('#skF_11', B_188, k9_relat_1('#skF_11', B_188), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_4'('#skF_11', B_188, k9_relat_1('#skF_11', B_188), '#skF_9'), k1_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_188)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_307])).
% 3.39/1.55  tff(c_590, plain, (![B_131]: (~r2_hidden('#skF_4'('#skF_11', B_131, k9_relat_1('#skF_11', B_131), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_131)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_317, c_586])).
% 3.39/1.55  tff(c_601, plain, (![B_189]: (~r2_hidden('#skF_4'('#skF_11', B_189, k9_relat_1('#skF_11', B_189), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_189)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_590])).
% 3.39/1.55  tff(c_605, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_4, c_601])).
% 3.39/1.55  tff(c_609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_177, c_605])).
% 3.39/1.55  tff(c_610, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_48])).
% 3.39/1.55  tff(c_692, plain, (![A_220, B_221, D_222]: (r2_hidden(k4_tarski('#skF_4'(A_220, B_221, k9_relat_1(A_220, B_221), D_222), D_222), A_220) | ~r2_hidden(D_222, k9_relat_1(A_220, B_221)) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.55  tff(c_706, plain, (![A_220, B_221, D_222]: (r2_hidden('#skF_4'(A_220, B_221, k9_relat_1(A_220, B_221), D_222), k1_relat_1(A_220)) | ~r2_hidden(D_222, k9_relat_1(A_220, B_221)) | ~v1_relat_1(A_220))), inference(resolution, [status(thm)], [c_692, c_22])).
% 3.39/1.55  tff(c_611, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_48])).
% 3.39/1.55  tff(c_46, plain, (![D_64]: (~r2_hidden(D_64, '#skF_10') | ~r2_hidden(k4_tarski(D_64, '#skF_9'), '#skF_11') | ~r2_hidden(D_64, k1_relat_1('#skF_11')) | r2_hidden('#skF_12', k1_relat_1('#skF_11')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_667, plain, (![D_64]: (~r2_hidden(D_64, '#skF_10') | ~r2_hidden(k4_tarski(D_64, '#skF_9'), '#skF_11') | ~r2_hidden(D_64, k1_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_611, c_46])).
% 3.39/1.55  tff(c_696, plain, (![B_221]: (~r2_hidden('#skF_4'('#skF_11', B_221, k9_relat_1('#skF_11', B_221), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_4'('#skF_11', B_221, k9_relat_1('#skF_11', B_221), '#skF_9'), k1_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_221)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_692, c_667])).
% 3.39/1.55  tff(c_856, plain, (![B_275]: (~r2_hidden('#skF_4'('#skF_11', B_275, k9_relat_1('#skF_11', B_275), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_4'('#skF_11', B_275, k9_relat_1('#skF_11', B_275), '#skF_9'), k1_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_275)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_696])).
% 3.39/1.55  tff(c_860, plain, (![B_221]: (~r2_hidden('#skF_4'('#skF_11', B_221, k9_relat_1('#skF_11', B_221), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_221)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_706, c_856])).
% 3.39/1.55  tff(c_871, plain, (![B_276]: (~r2_hidden('#skF_4'('#skF_11', B_276, k9_relat_1('#skF_11', B_276), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_276)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_860])).
% 3.39/1.55  tff(c_875, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_4, c_871])).
% 3.39/1.55  tff(c_879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_610, c_875])).
% 3.39/1.55  tff(c_880, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_40])).
% 3.39/1.55  tff(c_955, plain, (![A_308, B_309, D_310]: (r2_hidden(k4_tarski('#skF_4'(A_308, B_309, k9_relat_1(A_308, B_309), D_310), D_310), A_308) | ~r2_hidden(D_310, k9_relat_1(A_308, B_309)) | ~v1_relat_1(A_308))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.55  tff(c_972, plain, (![A_308, B_309, D_310]: (r2_hidden('#skF_4'(A_308, B_309, k9_relat_1(A_308, B_309), D_310), k1_relat_1(A_308)) | ~r2_hidden(D_310, k9_relat_1(A_308, B_309)) | ~v1_relat_1(A_308))), inference(resolution, [status(thm)], [c_955, c_22])).
% 3.39/1.55  tff(c_881, plain, (~r2_hidden('#skF_12', '#skF_10')), inference(splitRight, [status(thm)], [c_40])).
% 3.39/1.55  tff(c_38, plain, (![D_64]: (~r2_hidden(D_64, '#skF_10') | ~r2_hidden(k4_tarski(D_64, '#skF_9'), '#skF_11') | ~r2_hidden(D_64, k1_relat_1('#skF_11')) | r2_hidden('#skF_12', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.55  tff(c_891, plain, (![D_64]: (~r2_hidden(D_64, '#skF_10') | ~r2_hidden(k4_tarski(D_64, '#skF_9'), '#skF_11') | ~r2_hidden(D_64, k1_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_881, c_38])).
% 3.39/1.55  tff(c_963, plain, (![B_309]: (~r2_hidden('#skF_4'('#skF_11', B_309, k9_relat_1('#skF_11', B_309), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_4'('#skF_11', B_309, k9_relat_1('#skF_11', B_309), '#skF_9'), k1_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_309)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_955, c_891])).
% 3.39/1.55  tff(c_1037, plain, (![B_335]: (~r2_hidden('#skF_4'('#skF_11', B_335, k9_relat_1('#skF_11', B_335), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_4'('#skF_11', B_335, k9_relat_1('#skF_11', B_335), '#skF_9'), k1_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_335)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_963])).
% 3.39/1.55  tff(c_1041, plain, (![B_309]: (~r2_hidden('#skF_4'('#skF_11', B_309, k9_relat_1('#skF_11', B_309), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_309)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_972, c_1037])).
% 3.39/1.55  tff(c_1052, plain, (![B_336]: (~r2_hidden('#skF_4'('#skF_11', B_336, k9_relat_1('#skF_11', B_336), '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_11', B_336)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1041])).
% 3.39/1.55  tff(c_1056, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_4, c_1052])).
% 3.39/1.55  tff(c_1060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_880, c_1056])).
% 3.39/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.55  
% 3.39/1.55  Inference rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Ref     : 0
% 3.39/1.55  #Sup     : 219
% 3.39/1.55  #Fact    : 0
% 3.39/1.55  #Define  : 0
% 3.39/1.55  #Split   : 3
% 3.39/1.55  #Chain   : 0
% 3.39/1.55  #Close   : 0
% 3.39/1.55  
% 3.39/1.55  Ordering : KBO
% 3.39/1.55  
% 3.39/1.55  Simplification rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Subsume      : 9
% 3.39/1.55  #Demod        : 31
% 3.39/1.55  #Tautology    : 20
% 3.39/1.55  #SimpNegUnit  : 3
% 3.39/1.55  #BackRed      : 0
% 3.39/1.55  
% 3.39/1.55  #Partial instantiations: 0
% 3.39/1.55  #Strategies tried      : 1
% 3.39/1.55  
% 3.39/1.55  Timing (in seconds)
% 3.39/1.55  ----------------------
% 3.39/1.55  Preprocessing        : 0.29
% 3.39/1.55  Parsing              : 0.15
% 3.39/1.55  CNF conversion       : 0.03
% 3.39/1.55  Main loop            : 0.48
% 3.39/1.55  Inferencing          : 0.19
% 3.39/1.55  Reduction            : 0.12
% 3.39/1.55  Demodulation         : 0.08
% 3.39/1.55  BG Simplification    : 0.03
% 3.39/1.55  Subsumption          : 0.10
% 3.39/1.55  Abstraction          : 0.03
% 3.39/1.55  MUC search           : 0.00
% 3.39/1.55  Cooper               : 0.00
% 3.39/1.55  Total                : 0.80
% 3.39/1.55  Index Insertion      : 0.00
% 3.39/1.55  Index Deletion       : 0.00
% 3.39/1.55  Index Matching       : 0.00
% 3.39/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
