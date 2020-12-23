%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:18 EST 2020

% Result     : Theorem 10.57s
% Output     : CNFRefutation 10.57s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 400 expanded)
%              Number of leaves         :   25 ( 148 expanded)
%              Depth                    :   20
%              Number of atoms          :  243 (1348 expanded)
%              Number of equality atoms :    1 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(k8_relat_1(A_41,B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden('#skF_1'(A_52,B_53),B_53)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_42,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_24,B_34] :
      ( r2_hidden(k4_tarski('#skF_6'(A_24,B_34),'#skF_7'(A_24,B_34)),A_24)
      | r1_tarski(A_24,B_34)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [E_69,A_70,D_71,B_72] :
      ( r2_hidden(E_69,A_70)
      | ~ r2_hidden(k4_tarski(D_71,E_69),k8_relat_1(A_70,B_72))
      | ~ v1_relat_1(k8_relat_1(A_70,B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_435,plain,(
    ! [A_143,B_144,B_145] :
      ( r2_hidden('#skF_7'(k8_relat_1(A_143,B_144),B_145),A_143)
      | ~ v1_relat_1(B_144)
      | r1_tarski(k8_relat_1(A_143,B_144),B_145)
      | ~ v1_relat_1(k8_relat_1(A_143,B_144)) ) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_963,plain,(
    ! [A_241,B_242,B_243,B_244] :
      ( r2_hidden('#skF_7'(k8_relat_1(A_241,B_242),B_243),B_244)
      | ~ r1_tarski(A_241,B_244)
      | ~ v1_relat_1(B_242)
      | r1_tarski(k8_relat_1(A_241,B_242),B_243)
      | ~ v1_relat_1(k8_relat_1(A_241,B_242)) ) ),
    inference(resolution,[status(thm)],[c_435,c_2])).

tff(c_1733,plain,(
    ! [B_372,B_370,A_368,B_371,B_369] :
      ( r2_hidden('#skF_7'(k8_relat_1(A_368,B_369),B_370),B_372)
      | ~ r1_tarski(B_371,B_372)
      | ~ r1_tarski(A_368,B_371)
      | ~ v1_relat_1(B_369)
      | r1_tarski(k8_relat_1(A_368,B_369),B_370)
      | ~ v1_relat_1(k8_relat_1(A_368,B_369)) ) ),
    inference(resolution,[status(thm)],[c_963,c_2])).

tff(c_1775,plain,(
    ! [A_368,B_369,B_370] :
      ( r2_hidden('#skF_7'(k8_relat_1(A_368,B_369),B_370),'#skF_9')
      | ~ r1_tarski(A_368,'#skF_8')
      | ~ v1_relat_1(B_369)
      | r1_tarski(k8_relat_1(A_368,B_369),B_370)
      | ~ v1_relat_1(k8_relat_1(A_368,B_369)) ) ),
    inference(resolution,[status(thm)],[c_38,c_1733])).

tff(c_40,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(k4_tarski('#skF_6'(A_61,B_62),'#skF_7'(A_61,B_62)),A_61)
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_251,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden(k4_tarski('#skF_6'(A_110,B_111),'#skF_7'(A_110,B_111)),B_112)
      | ~ r1_tarski(A_110,B_112)
      | r1_tarski(A_110,B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_535,plain,(
    ! [A_178,B_179,B_180,B_181] :
      ( r2_hidden(k4_tarski('#skF_6'(A_178,B_179),'#skF_7'(A_178,B_179)),B_180)
      | ~ r1_tarski(B_181,B_180)
      | ~ r1_tarski(A_178,B_181)
      | r1_tarski(A_178,B_179)
      | ~ v1_relat_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_561,plain,(
    ! [A_178,B_179] :
      ( r2_hidden(k4_tarski('#skF_6'(A_178,B_179),'#skF_7'(A_178,B_179)),'#skF_11')
      | ~ r1_tarski(A_178,'#skF_10')
      | r1_tarski(A_178,B_179)
      | ~ v1_relat_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_40,c_535])).

tff(c_216,plain,(
    ! [D_99,E_100,A_101,B_102] :
      ( r2_hidden(k4_tarski(D_99,E_100),k8_relat_1(A_101,B_102))
      | ~ r2_hidden(k4_tarski(D_99,E_100),B_102)
      | ~ r2_hidden(E_100,A_101)
      | ~ v1_relat_1(k8_relat_1(A_101,B_102))
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_24,B_34] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_24,B_34),'#skF_7'(A_24,B_34)),B_34)
      | r1_tarski(A_24,B_34)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3061,plain,(
    ! [A_558,A_559,B_560] :
      ( r1_tarski(A_558,k8_relat_1(A_559,B_560))
      | ~ v1_relat_1(A_558)
      | ~ r2_hidden(k4_tarski('#skF_6'(A_558,k8_relat_1(A_559,B_560)),'#skF_7'(A_558,k8_relat_1(A_559,B_560))),B_560)
      | ~ r2_hidden('#skF_7'(A_558,k8_relat_1(A_559,B_560)),A_559)
      | ~ v1_relat_1(k8_relat_1(A_559,B_560))
      | ~ v1_relat_1(B_560) ) ),
    inference(resolution,[status(thm)],[c_216,c_28])).

tff(c_3081,plain,(
    ! [A_178,A_559] :
      ( ~ r2_hidden('#skF_7'(A_178,k8_relat_1(A_559,'#skF_11')),A_559)
      | ~ v1_relat_1(k8_relat_1(A_559,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ r1_tarski(A_178,'#skF_10')
      | r1_tarski(A_178,k8_relat_1(A_559,'#skF_11'))
      | ~ v1_relat_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_561,c_3061])).

tff(c_3277,plain,(
    ! [A_565,A_566] :
      ( ~ r2_hidden('#skF_7'(A_565,k8_relat_1(A_566,'#skF_11')),A_566)
      | ~ v1_relat_1(k8_relat_1(A_566,'#skF_11'))
      | ~ r1_tarski(A_565,'#skF_10')
      | r1_tarski(A_565,k8_relat_1(A_566,'#skF_11'))
      | ~ v1_relat_1(A_565) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3081])).

tff(c_3304,plain,(
    ! [A_368,B_369] :
      ( ~ v1_relat_1(k8_relat_1('#skF_9','#skF_11'))
      | ~ r1_tarski(k8_relat_1(A_368,B_369),'#skF_10')
      | ~ r1_tarski(A_368,'#skF_8')
      | ~ v1_relat_1(B_369)
      | r1_tarski(k8_relat_1(A_368,B_369),k8_relat_1('#skF_9','#skF_11'))
      | ~ v1_relat_1(k8_relat_1(A_368,B_369)) ) ),
    inference(resolution,[status(thm)],[c_1775,c_3277])).

tff(c_6404,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_9','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_3304])).

tff(c_6407,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_6404])).

tff(c_6411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6407])).

tff(c_6413,plain,(
    v1_relat_1(k8_relat_1('#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_3304])).

tff(c_71,plain,(
    ! [A_61,B_62,B_2] :
      ( r2_hidden(k4_tarski('#skF_6'(A_61,B_62),'#skF_7'(A_61,B_62)),B_2)
      | ~ r1_tarski(A_61,B_2)
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_4477,plain,(
    ! [A_613,A_614,B_615] :
      ( ~ r2_hidden('#skF_7'(A_613,k8_relat_1(A_614,B_615)),A_614)
      | ~ v1_relat_1(k8_relat_1(A_614,B_615))
      | ~ v1_relat_1(B_615)
      | ~ r1_tarski(A_613,B_615)
      | r1_tarski(A_613,k8_relat_1(A_614,B_615))
      | ~ v1_relat_1(A_613) ) ),
    inference(resolution,[status(thm)],[c_71,c_3061])).

tff(c_8281,plain,(
    ! [B_665,A_666,B_667] :
      ( ~ v1_relat_1(k8_relat_1('#skF_9',B_665))
      | ~ v1_relat_1(B_665)
      | ~ r1_tarski(k8_relat_1(A_666,B_667),B_665)
      | ~ r1_tarski(A_666,'#skF_8')
      | ~ v1_relat_1(B_667)
      | r1_tarski(k8_relat_1(A_666,B_667),k8_relat_1('#skF_9',B_665))
      | ~ v1_relat_1(k8_relat_1(A_666,B_667)) ) ),
    inference(resolution,[status(thm)],[c_1775,c_4477])).

tff(c_36,plain,(
    ~ r1_tarski(k8_relat_1('#skF_8','#skF_10'),k8_relat_1('#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8392,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_9','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ r1_tarski(k8_relat_1('#skF_8','#skF_10'),'#skF_11')
    | ~ r1_tarski('#skF_8','#skF_8')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10')) ),
    inference(resolution,[status(thm)],[c_8281,c_36])).

tff(c_8469,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_8','#skF_10'),'#skF_11')
    | ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_53,c_42,c_6413,c_8392])).

tff(c_9499,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_8469])).

tff(c_9697,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_9499])).

tff(c_9701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9697])).

tff(c_9703,plain,(
    v1_relat_1(k8_relat_1('#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_8469])).

tff(c_97,plain,(
    ! [A_70,B_72,B_34] :
      ( r2_hidden('#skF_7'(k8_relat_1(A_70,B_72),B_34),A_70)
      | ~ v1_relat_1(B_72)
      | r1_tarski(k8_relat_1(A_70,B_72),B_34)
      | ~ v1_relat_1(k8_relat_1(A_70,B_72)) ) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_3104,plain,(
    ! [A_561,A_562] :
      ( ~ r2_hidden('#skF_7'(A_561,k8_relat_1(A_562,A_561)),A_562)
      | ~ v1_relat_1(k8_relat_1(A_562,A_561))
      | r1_tarski(A_561,k8_relat_1(A_562,A_561))
      | ~ v1_relat_1(A_561) ) ),
    inference(resolution,[status(thm)],[c_30,c_3061])).

tff(c_3135,plain,(
    ! [A_563,B_564] :
      ( ~ v1_relat_1(k8_relat_1(A_563,k8_relat_1(A_563,B_564)))
      | ~ v1_relat_1(B_564)
      | r1_tarski(k8_relat_1(A_563,B_564),k8_relat_1(A_563,k8_relat_1(A_563,B_564)))
      | ~ v1_relat_1(k8_relat_1(A_563,B_564)) ) ),
    inference(resolution,[status(thm)],[c_97,c_3104])).

tff(c_34,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k8_relat_1(A_43,B_44),B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_58,B_59,B_60] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_60)
      | ~ r1_tarski(A_58,B_60)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_79,plain,(
    ! [A_65,B_66,B_67,B_68] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_67)
      | ~ r1_tarski(B_68,B_67)
      | ~ r1_tarski(A_65,B_68)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_233,plain,(
    ! [A_103,B_104,B_105,A_106] :
      ( r2_hidden('#skF_1'(A_103,B_104),B_105)
      | ~ r1_tarski(A_103,k8_relat_1(A_106,B_105))
      | r1_tarski(A_103,B_104)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_242,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_107,B_108),B_109),B_108)
      | r1_tarski(k8_relat_1(A_107,B_108),B_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_53,c_233])).

tff(c_308,plain,(
    ! [A_121,B_122,B_123,B_124] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_121,B_122),B_123),B_124)
      | ~ r1_tarski(B_122,B_124)
      | r1_tarski(k8_relat_1(A_121,B_122),B_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_242,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_317,plain,(
    ! [B_125,B_126,A_127] :
      ( ~ r1_tarski(B_125,B_126)
      | r1_tarski(k8_relat_1(A_127,B_125),B_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_308,c_4])).

tff(c_98,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),'#skF_11')
      | ~ r1_tarski(A_73,'#skF_10')
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_107,plain,(
    ! [A_75] :
      ( ~ r1_tarski(A_75,'#skF_10')
      | r1_tarski(A_75,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_66,plain,(
    ! [A_58,B_59,B_2,B_60] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_2)
      | ~ r1_tarski(B_60,B_2)
      | ~ r1_tarski(A_58,B_60)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_110,plain,(
    ! [A_58,B_59,A_75] :
      ( r2_hidden('#skF_1'(A_58,B_59),'#skF_11')
      | ~ r1_tarski(A_58,A_75)
      | r1_tarski(A_58,B_59)
      | ~ r1_tarski(A_75,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_107,c_66])).

tff(c_494,plain,(
    ! [A_166,B_167,B_168,B_169] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_166,B_167),B_168),'#skF_11')
      | r1_tarski(k8_relat_1(A_166,B_167),B_168)
      | ~ r1_tarski(B_169,'#skF_10')
      | ~ r1_tarski(B_167,B_169)
      | ~ v1_relat_1(B_167) ) ),
    inference(resolution,[status(thm)],[c_317,c_110])).

tff(c_503,plain,(
    ! [A_166,B_167,B_168,A_43] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_166,B_167),B_168),'#skF_11')
      | r1_tarski(k8_relat_1(A_166,B_167),B_168)
      | ~ r1_tarski(B_167,k8_relat_1(A_43,'#skF_10'))
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_494])).

tff(c_522,plain,(
    ! [A_174,B_175,B_176,A_177] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_174,B_175),B_176),'#skF_11')
      | r1_tarski(k8_relat_1(A_174,B_175),B_176)
      | ~ r1_tarski(B_175,k8_relat_1(A_177,'#skF_10'))
      | ~ v1_relat_1(B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_503])).

tff(c_899,plain,(
    ! [A_229,A_230,B_231] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_229,k8_relat_1(A_230,'#skF_10')),B_231),'#skF_11')
      | r1_tarski(k8_relat_1(A_229,k8_relat_1(A_230,'#skF_10')),B_231)
      | ~ v1_relat_1(k8_relat_1(A_230,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_53,c_522])).

tff(c_908,plain,(
    ! [A_232,A_233] :
      ( r1_tarski(k8_relat_1(A_232,k8_relat_1(A_233,'#skF_10')),'#skF_11')
      | ~ v1_relat_1(k8_relat_1(A_233,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_899,c_4])).

tff(c_935,plain,(
    ! [A_58,B_59,A_232,A_233] :
      ( r2_hidden('#skF_1'(A_58,B_59),'#skF_11')
      | ~ r1_tarski(A_58,k8_relat_1(A_232,k8_relat_1(A_233,'#skF_10')))
      | r1_tarski(A_58,B_59)
      | ~ v1_relat_1(k8_relat_1(A_233,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_908,c_66])).

tff(c_3199,plain,(
    ! [A_563,B_59] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_563,'#skF_10'),B_59),'#skF_11')
      | r1_tarski(k8_relat_1(A_563,'#skF_10'),B_59)
      | ~ v1_relat_1(k8_relat_1(A_563,k8_relat_1(A_563,'#skF_10')))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1(k8_relat_1(A_563,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_3135,c_935])).

tff(c_3588,plain,(
    ! [A_571,B_572] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_571,'#skF_10'),B_572),'#skF_11')
      | r1_tarski(k8_relat_1(A_571,'#skF_10'),B_572)
      | ~ v1_relat_1(k8_relat_1(A_571,k8_relat_1(A_571,'#skF_10')))
      | ~ v1_relat_1(k8_relat_1(A_571,'#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3199])).

tff(c_3593,plain,(
    ! [A_573,B_574] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_573,'#skF_10'),B_574),'#skF_11')
      | r1_tarski(k8_relat_1(A_573,'#skF_10'),B_574)
      | ~ v1_relat_1(k8_relat_1(A_573,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_32,c_3588])).

tff(c_3880,plain,(
    ! [A_586,B_587,B_588] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_586,'#skF_10'),B_587),B_588)
      | ~ r1_tarski('#skF_11',B_588)
      | r1_tarski(k8_relat_1(A_586,'#skF_10'),B_587)
      | ~ v1_relat_1(k8_relat_1(A_586,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_3593,c_2])).

tff(c_3891,plain,(
    ! [B_588,A_586] :
      ( ~ r1_tarski('#skF_11',B_588)
      | r1_tarski(k8_relat_1(A_586,'#skF_10'),B_588)
      | ~ v1_relat_1(k8_relat_1(A_586,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_3880,c_4])).

tff(c_9702,plain,(
    ~ r1_tarski(k8_relat_1('#skF_8','#skF_10'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_8469])).

tff(c_9711,plain,
    ( ~ r1_tarski('#skF_11','#skF_11')
    | ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10')) ),
    inference(resolution,[status(thm)],[c_3891,c_9702])).

tff(c_9733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9703,c_53,c_9711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:28:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.57/3.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.57/3.63  
% 10.57/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.57/3.63  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1
% 10.57/3.63  
% 10.57/3.63  %Foreground sorts:
% 10.57/3.63  
% 10.57/3.63  
% 10.57/3.63  %Background operators:
% 10.57/3.63  
% 10.57/3.63  
% 10.57/3.63  %Foreground operators:
% 10.57/3.63  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 10.57/3.63  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.57/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.57/3.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.57/3.63  tff('#skF_11', type, '#skF_11': $i).
% 10.57/3.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.57/3.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.57/3.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.57/3.63  tff('#skF_10', type, '#skF_10': $i).
% 10.57/3.63  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.57/3.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.57/3.63  tff('#skF_9', type, '#skF_9': $i).
% 10.57/3.63  tff('#skF_8', type, '#skF_8': $i).
% 10.57/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.57/3.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.57/3.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.57/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.57/3.63  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.57/3.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.57/3.63  
% 10.57/3.65  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 10.57/3.65  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 10.57/3.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.57/3.65  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 10.57/3.65  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 10.57/3.65  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 10.57/3.65  tff(c_44, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.57/3.65  tff(c_32, plain, (![A_41, B_42]: (v1_relat_1(k8_relat_1(A_41, B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.57/3.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.57/3.65  tff(c_48, plain, (![A_52, B_53]: (~r2_hidden('#skF_1'(A_52, B_53), B_53) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.57/3.65  tff(c_53, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_48])).
% 10.57/3.65  tff(c_42, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.57/3.65  tff(c_38, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.57/3.65  tff(c_30, plain, (![A_24, B_34]: (r2_hidden(k4_tarski('#skF_6'(A_24, B_34), '#skF_7'(A_24, B_34)), A_24) | r1_tarski(A_24, B_34) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.57/3.65  tff(c_92, plain, (![E_69, A_70, D_71, B_72]: (r2_hidden(E_69, A_70) | ~r2_hidden(k4_tarski(D_71, E_69), k8_relat_1(A_70, B_72)) | ~v1_relat_1(k8_relat_1(A_70, B_72)) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.57/3.65  tff(c_435, plain, (![A_143, B_144, B_145]: (r2_hidden('#skF_7'(k8_relat_1(A_143, B_144), B_145), A_143) | ~v1_relat_1(B_144) | r1_tarski(k8_relat_1(A_143, B_144), B_145) | ~v1_relat_1(k8_relat_1(A_143, B_144)))), inference(resolution, [status(thm)], [c_30, c_92])).
% 10.57/3.65  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.57/3.65  tff(c_963, plain, (![A_241, B_242, B_243, B_244]: (r2_hidden('#skF_7'(k8_relat_1(A_241, B_242), B_243), B_244) | ~r1_tarski(A_241, B_244) | ~v1_relat_1(B_242) | r1_tarski(k8_relat_1(A_241, B_242), B_243) | ~v1_relat_1(k8_relat_1(A_241, B_242)))), inference(resolution, [status(thm)], [c_435, c_2])).
% 10.57/3.65  tff(c_1733, plain, (![B_372, B_370, A_368, B_371, B_369]: (r2_hidden('#skF_7'(k8_relat_1(A_368, B_369), B_370), B_372) | ~r1_tarski(B_371, B_372) | ~r1_tarski(A_368, B_371) | ~v1_relat_1(B_369) | r1_tarski(k8_relat_1(A_368, B_369), B_370) | ~v1_relat_1(k8_relat_1(A_368, B_369)))), inference(resolution, [status(thm)], [c_963, c_2])).
% 10.57/3.65  tff(c_1775, plain, (![A_368, B_369, B_370]: (r2_hidden('#skF_7'(k8_relat_1(A_368, B_369), B_370), '#skF_9') | ~r1_tarski(A_368, '#skF_8') | ~v1_relat_1(B_369) | r1_tarski(k8_relat_1(A_368, B_369), B_370) | ~v1_relat_1(k8_relat_1(A_368, B_369)))), inference(resolution, [status(thm)], [c_38, c_1733])).
% 10.57/3.65  tff(c_40, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.57/3.65  tff(c_68, plain, (![A_61, B_62]: (r2_hidden(k4_tarski('#skF_6'(A_61, B_62), '#skF_7'(A_61, B_62)), A_61) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.57/3.65  tff(c_251, plain, (![A_110, B_111, B_112]: (r2_hidden(k4_tarski('#skF_6'(A_110, B_111), '#skF_7'(A_110, B_111)), B_112) | ~r1_tarski(A_110, B_112) | r1_tarski(A_110, B_111) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_68, c_2])).
% 10.57/3.65  tff(c_535, plain, (![A_178, B_179, B_180, B_181]: (r2_hidden(k4_tarski('#skF_6'(A_178, B_179), '#skF_7'(A_178, B_179)), B_180) | ~r1_tarski(B_181, B_180) | ~r1_tarski(A_178, B_181) | r1_tarski(A_178, B_179) | ~v1_relat_1(A_178))), inference(resolution, [status(thm)], [c_251, c_2])).
% 10.57/3.65  tff(c_561, plain, (![A_178, B_179]: (r2_hidden(k4_tarski('#skF_6'(A_178, B_179), '#skF_7'(A_178, B_179)), '#skF_11') | ~r1_tarski(A_178, '#skF_10') | r1_tarski(A_178, B_179) | ~v1_relat_1(A_178))), inference(resolution, [status(thm)], [c_40, c_535])).
% 10.57/3.65  tff(c_216, plain, (![D_99, E_100, A_101, B_102]: (r2_hidden(k4_tarski(D_99, E_100), k8_relat_1(A_101, B_102)) | ~r2_hidden(k4_tarski(D_99, E_100), B_102) | ~r2_hidden(E_100, A_101) | ~v1_relat_1(k8_relat_1(A_101, B_102)) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.57/3.65  tff(c_28, plain, (![A_24, B_34]: (~r2_hidden(k4_tarski('#skF_6'(A_24, B_34), '#skF_7'(A_24, B_34)), B_34) | r1_tarski(A_24, B_34) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.57/3.65  tff(c_3061, plain, (![A_558, A_559, B_560]: (r1_tarski(A_558, k8_relat_1(A_559, B_560)) | ~v1_relat_1(A_558) | ~r2_hidden(k4_tarski('#skF_6'(A_558, k8_relat_1(A_559, B_560)), '#skF_7'(A_558, k8_relat_1(A_559, B_560))), B_560) | ~r2_hidden('#skF_7'(A_558, k8_relat_1(A_559, B_560)), A_559) | ~v1_relat_1(k8_relat_1(A_559, B_560)) | ~v1_relat_1(B_560))), inference(resolution, [status(thm)], [c_216, c_28])).
% 10.57/3.65  tff(c_3081, plain, (![A_178, A_559]: (~r2_hidden('#skF_7'(A_178, k8_relat_1(A_559, '#skF_11')), A_559) | ~v1_relat_1(k8_relat_1(A_559, '#skF_11')) | ~v1_relat_1('#skF_11') | ~r1_tarski(A_178, '#skF_10') | r1_tarski(A_178, k8_relat_1(A_559, '#skF_11')) | ~v1_relat_1(A_178))), inference(resolution, [status(thm)], [c_561, c_3061])).
% 10.57/3.65  tff(c_3277, plain, (![A_565, A_566]: (~r2_hidden('#skF_7'(A_565, k8_relat_1(A_566, '#skF_11')), A_566) | ~v1_relat_1(k8_relat_1(A_566, '#skF_11')) | ~r1_tarski(A_565, '#skF_10') | r1_tarski(A_565, k8_relat_1(A_566, '#skF_11')) | ~v1_relat_1(A_565))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3081])).
% 10.57/3.65  tff(c_3304, plain, (![A_368, B_369]: (~v1_relat_1(k8_relat_1('#skF_9', '#skF_11')) | ~r1_tarski(k8_relat_1(A_368, B_369), '#skF_10') | ~r1_tarski(A_368, '#skF_8') | ~v1_relat_1(B_369) | r1_tarski(k8_relat_1(A_368, B_369), k8_relat_1('#skF_9', '#skF_11')) | ~v1_relat_1(k8_relat_1(A_368, B_369)))), inference(resolution, [status(thm)], [c_1775, c_3277])).
% 10.57/3.65  tff(c_6404, plain, (~v1_relat_1(k8_relat_1('#skF_9', '#skF_11'))), inference(splitLeft, [status(thm)], [c_3304])).
% 10.57/3.65  tff(c_6407, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_6404])).
% 10.57/3.65  tff(c_6411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6407])).
% 10.57/3.65  tff(c_6413, plain, (v1_relat_1(k8_relat_1('#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_3304])).
% 10.57/3.65  tff(c_71, plain, (![A_61, B_62, B_2]: (r2_hidden(k4_tarski('#skF_6'(A_61, B_62), '#skF_7'(A_61, B_62)), B_2) | ~r1_tarski(A_61, B_2) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_68, c_2])).
% 10.57/3.65  tff(c_4477, plain, (![A_613, A_614, B_615]: (~r2_hidden('#skF_7'(A_613, k8_relat_1(A_614, B_615)), A_614) | ~v1_relat_1(k8_relat_1(A_614, B_615)) | ~v1_relat_1(B_615) | ~r1_tarski(A_613, B_615) | r1_tarski(A_613, k8_relat_1(A_614, B_615)) | ~v1_relat_1(A_613))), inference(resolution, [status(thm)], [c_71, c_3061])).
% 10.57/3.65  tff(c_8281, plain, (![B_665, A_666, B_667]: (~v1_relat_1(k8_relat_1('#skF_9', B_665)) | ~v1_relat_1(B_665) | ~r1_tarski(k8_relat_1(A_666, B_667), B_665) | ~r1_tarski(A_666, '#skF_8') | ~v1_relat_1(B_667) | r1_tarski(k8_relat_1(A_666, B_667), k8_relat_1('#skF_9', B_665)) | ~v1_relat_1(k8_relat_1(A_666, B_667)))), inference(resolution, [status(thm)], [c_1775, c_4477])).
% 10.57/3.65  tff(c_36, plain, (~r1_tarski(k8_relat_1('#skF_8', '#skF_10'), k8_relat_1('#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.57/3.65  tff(c_8392, plain, (~v1_relat_1(k8_relat_1('#skF_9', '#skF_11')) | ~v1_relat_1('#skF_11') | ~r1_tarski(k8_relat_1('#skF_8', '#skF_10'), '#skF_11') | ~r1_tarski('#skF_8', '#skF_8') | ~v1_relat_1('#skF_10') | ~v1_relat_1(k8_relat_1('#skF_8', '#skF_10'))), inference(resolution, [status(thm)], [c_8281, c_36])).
% 10.57/3.65  tff(c_8469, plain, (~r1_tarski(k8_relat_1('#skF_8', '#skF_10'), '#skF_11') | ~v1_relat_1(k8_relat_1('#skF_8', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_53, c_42, c_6413, c_8392])).
% 10.57/3.65  tff(c_9499, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_8469])).
% 10.57/3.65  tff(c_9697, plain, (~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_9499])).
% 10.57/3.65  tff(c_9701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_9697])).
% 10.57/3.65  tff(c_9703, plain, (v1_relat_1(k8_relat_1('#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_8469])).
% 10.57/3.65  tff(c_97, plain, (![A_70, B_72, B_34]: (r2_hidden('#skF_7'(k8_relat_1(A_70, B_72), B_34), A_70) | ~v1_relat_1(B_72) | r1_tarski(k8_relat_1(A_70, B_72), B_34) | ~v1_relat_1(k8_relat_1(A_70, B_72)))), inference(resolution, [status(thm)], [c_30, c_92])).
% 10.57/3.65  tff(c_3104, plain, (![A_561, A_562]: (~r2_hidden('#skF_7'(A_561, k8_relat_1(A_562, A_561)), A_562) | ~v1_relat_1(k8_relat_1(A_562, A_561)) | r1_tarski(A_561, k8_relat_1(A_562, A_561)) | ~v1_relat_1(A_561))), inference(resolution, [status(thm)], [c_30, c_3061])).
% 10.57/3.65  tff(c_3135, plain, (![A_563, B_564]: (~v1_relat_1(k8_relat_1(A_563, k8_relat_1(A_563, B_564))) | ~v1_relat_1(B_564) | r1_tarski(k8_relat_1(A_563, B_564), k8_relat_1(A_563, k8_relat_1(A_563, B_564))) | ~v1_relat_1(k8_relat_1(A_563, B_564)))), inference(resolution, [status(thm)], [c_97, c_3104])).
% 10.57/3.65  tff(c_34, plain, (![A_43, B_44]: (r1_tarski(k8_relat_1(A_43, B_44), B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.57/3.65  tff(c_54, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.57/3.65  tff(c_59, plain, (![A_58, B_59, B_60]: (r2_hidden('#skF_1'(A_58, B_59), B_60) | ~r1_tarski(A_58, B_60) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_6, c_54])).
% 10.57/3.65  tff(c_79, plain, (![A_65, B_66, B_67, B_68]: (r2_hidden('#skF_1'(A_65, B_66), B_67) | ~r1_tarski(B_68, B_67) | ~r1_tarski(A_65, B_68) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_59, c_2])).
% 10.57/3.65  tff(c_233, plain, (![A_103, B_104, B_105, A_106]: (r2_hidden('#skF_1'(A_103, B_104), B_105) | ~r1_tarski(A_103, k8_relat_1(A_106, B_105)) | r1_tarski(A_103, B_104) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_34, c_79])).
% 10.57/3.65  tff(c_242, plain, (![A_107, B_108, B_109]: (r2_hidden('#skF_1'(k8_relat_1(A_107, B_108), B_109), B_108) | r1_tarski(k8_relat_1(A_107, B_108), B_109) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_53, c_233])).
% 10.57/3.65  tff(c_308, plain, (![A_121, B_122, B_123, B_124]: (r2_hidden('#skF_1'(k8_relat_1(A_121, B_122), B_123), B_124) | ~r1_tarski(B_122, B_124) | r1_tarski(k8_relat_1(A_121, B_122), B_123) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_242, c_2])).
% 10.57/3.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.57/3.65  tff(c_317, plain, (![B_125, B_126, A_127]: (~r1_tarski(B_125, B_126) | r1_tarski(k8_relat_1(A_127, B_125), B_126) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_308, c_4])).
% 10.57/3.65  tff(c_98, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), '#skF_11') | ~r1_tarski(A_73, '#skF_10') | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_40, c_79])).
% 10.57/3.65  tff(c_107, plain, (![A_75]: (~r1_tarski(A_75, '#skF_10') | r1_tarski(A_75, '#skF_11'))), inference(resolution, [status(thm)], [c_98, c_4])).
% 10.57/3.65  tff(c_66, plain, (![A_58, B_59, B_2, B_60]: (r2_hidden('#skF_1'(A_58, B_59), B_2) | ~r1_tarski(B_60, B_2) | ~r1_tarski(A_58, B_60) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_59, c_2])).
% 10.57/3.65  tff(c_110, plain, (![A_58, B_59, A_75]: (r2_hidden('#skF_1'(A_58, B_59), '#skF_11') | ~r1_tarski(A_58, A_75) | r1_tarski(A_58, B_59) | ~r1_tarski(A_75, '#skF_10'))), inference(resolution, [status(thm)], [c_107, c_66])).
% 10.57/3.65  tff(c_494, plain, (![A_166, B_167, B_168, B_169]: (r2_hidden('#skF_1'(k8_relat_1(A_166, B_167), B_168), '#skF_11') | r1_tarski(k8_relat_1(A_166, B_167), B_168) | ~r1_tarski(B_169, '#skF_10') | ~r1_tarski(B_167, B_169) | ~v1_relat_1(B_167))), inference(resolution, [status(thm)], [c_317, c_110])).
% 10.57/3.65  tff(c_503, plain, (![A_166, B_167, B_168, A_43]: (r2_hidden('#skF_1'(k8_relat_1(A_166, B_167), B_168), '#skF_11') | r1_tarski(k8_relat_1(A_166, B_167), B_168) | ~r1_tarski(B_167, k8_relat_1(A_43, '#skF_10')) | ~v1_relat_1(B_167) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_494])).
% 10.57/3.65  tff(c_522, plain, (![A_174, B_175, B_176, A_177]: (r2_hidden('#skF_1'(k8_relat_1(A_174, B_175), B_176), '#skF_11') | r1_tarski(k8_relat_1(A_174, B_175), B_176) | ~r1_tarski(B_175, k8_relat_1(A_177, '#skF_10')) | ~v1_relat_1(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_503])).
% 10.57/3.65  tff(c_899, plain, (![A_229, A_230, B_231]: (r2_hidden('#skF_1'(k8_relat_1(A_229, k8_relat_1(A_230, '#skF_10')), B_231), '#skF_11') | r1_tarski(k8_relat_1(A_229, k8_relat_1(A_230, '#skF_10')), B_231) | ~v1_relat_1(k8_relat_1(A_230, '#skF_10')))), inference(resolution, [status(thm)], [c_53, c_522])).
% 10.57/3.65  tff(c_908, plain, (![A_232, A_233]: (r1_tarski(k8_relat_1(A_232, k8_relat_1(A_233, '#skF_10')), '#skF_11') | ~v1_relat_1(k8_relat_1(A_233, '#skF_10')))), inference(resolution, [status(thm)], [c_899, c_4])).
% 10.57/3.65  tff(c_935, plain, (![A_58, B_59, A_232, A_233]: (r2_hidden('#skF_1'(A_58, B_59), '#skF_11') | ~r1_tarski(A_58, k8_relat_1(A_232, k8_relat_1(A_233, '#skF_10'))) | r1_tarski(A_58, B_59) | ~v1_relat_1(k8_relat_1(A_233, '#skF_10')))), inference(resolution, [status(thm)], [c_908, c_66])).
% 10.57/3.65  tff(c_3199, plain, (![A_563, B_59]: (r2_hidden('#skF_1'(k8_relat_1(A_563, '#skF_10'), B_59), '#skF_11') | r1_tarski(k8_relat_1(A_563, '#skF_10'), B_59) | ~v1_relat_1(k8_relat_1(A_563, k8_relat_1(A_563, '#skF_10'))) | ~v1_relat_1('#skF_10') | ~v1_relat_1(k8_relat_1(A_563, '#skF_10')))), inference(resolution, [status(thm)], [c_3135, c_935])).
% 10.57/3.65  tff(c_3588, plain, (![A_571, B_572]: (r2_hidden('#skF_1'(k8_relat_1(A_571, '#skF_10'), B_572), '#skF_11') | r1_tarski(k8_relat_1(A_571, '#skF_10'), B_572) | ~v1_relat_1(k8_relat_1(A_571, k8_relat_1(A_571, '#skF_10'))) | ~v1_relat_1(k8_relat_1(A_571, '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3199])).
% 10.57/3.65  tff(c_3593, plain, (![A_573, B_574]: (r2_hidden('#skF_1'(k8_relat_1(A_573, '#skF_10'), B_574), '#skF_11') | r1_tarski(k8_relat_1(A_573, '#skF_10'), B_574) | ~v1_relat_1(k8_relat_1(A_573, '#skF_10')))), inference(resolution, [status(thm)], [c_32, c_3588])).
% 10.57/3.65  tff(c_3880, plain, (![A_586, B_587, B_588]: (r2_hidden('#skF_1'(k8_relat_1(A_586, '#skF_10'), B_587), B_588) | ~r1_tarski('#skF_11', B_588) | r1_tarski(k8_relat_1(A_586, '#skF_10'), B_587) | ~v1_relat_1(k8_relat_1(A_586, '#skF_10')))), inference(resolution, [status(thm)], [c_3593, c_2])).
% 10.57/3.65  tff(c_3891, plain, (![B_588, A_586]: (~r1_tarski('#skF_11', B_588) | r1_tarski(k8_relat_1(A_586, '#skF_10'), B_588) | ~v1_relat_1(k8_relat_1(A_586, '#skF_10')))), inference(resolution, [status(thm)], [c_3880, c_4])).
% 10.57/3.65  tff(c_9702, plain, (~r1_tarski(k8_relat_1('#skF_8', '#skF_10'), '#skF_11')), inference(splitRight, [status(thm)], [c_8469])).
% 10.57/3.65  tff(c_9711, plain, (~r1_tarski('#skF_11', '#skF_11') | ~v1_relat_1(k8_relat_1('#skF_8', '#skF_10'))), inference(resolution, [status(thm)], [c_3891, c_9702])).
% 10.57/3.65  tff(c_9733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9703, c_53, c_9711])).
% 10.57/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.57/3.65  
% 10.57/3.65  Inference rules
% 10.57/3.65  ----------------------
% 10.57/3.65  #Ref     : 0
% 10.57/3.65  #Sup     : 2424
% 10.57/3.65  #Fact    : 0
% 10.57/3.65  #Define  : 0
% 10.57/3.65  #Split   : 18
% 10.57/3.65  #Chain   : 0
% 10.57/3.65  #Close   : 0
% 10.57/3.65  
% 10.57/3.65  Ordering : KBO
% 10.57/3.65  
% 10.57/3.65  Simplification rules
% 10.57/3.65  ----------------------
% 10.57/3.65  #Subsume      : 924
% 10.57/3.65  #Demod        : 2040
% 10.57/3.65  #Tautology    : 75
% 10.57/3.65  #SimpNegUnit  : 0
% 10.57/3.65  #BackRed      : 0
% 10.57/3.65  
% 10.57/3.65  #Partial instantiations: 0
% 10.57/3.65  #Strategies tried      : 1
% 10.57/3.65  
% 10.57/3.65  Timing (in seconds)
% 10.57/3.65  ----------------------
% 10.57/3.65  Preprocessing        : 0.29
% 10.57/3.65  Parsing              : 0.15
% 10.57/3.65  CNF conversion       : 0.03
% 10.57/3.65  Main loop            : 2.59
% 10.57/3.65  Inferencing          : 0.54
% 10.57/3.65  Reduction            : 0.57
% 10.57/3.65  Demodulation         : 0.37
% 10.57/3.65  BG Simplification    : 0.08
% 10.57/3.65  Subsumption          : 1.28
% 10.57/3.66  Abstraction          : 0.09
% 10.57/3.66  MUC search           : 0.00
% 10.57/3.66  Cooper               : 0.00
% 10.57/3.66  Total                : 2.91
% 10.57/3.66  Index Insertion      : 0.00
% 10.57/3.66  Index Deletion       : 0.00
% 10.57/3.66  Index Matching       : 0.00
% 10.57/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
