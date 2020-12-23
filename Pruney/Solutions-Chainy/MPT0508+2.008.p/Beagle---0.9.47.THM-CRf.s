%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:55 EST 2020

% Result     : Theorem 11.24s
% Output     : CNFRefutation 11.24s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( v1_relat_1(k7_relat_1(A_42,B_43))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r1_tarski(A_53,B_54) ) ),
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
    ! [A_25,B_35] :
      ( r2_hidden(k4_tarski('#skF_6'(A_25,B_35),'#skF_7'(A_25,B_35)),A_25)
      | r1_tarski(A_25,B_35)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [D_70,B_71,E_72,A_73] :
      ( r2_hidden(D_70,B_71)
      | ~ r2_hidden(k4_tarski(D_70,E_72),k7_relat_1(A_73,B_71))
      | ~ v1_relat_1(k7_relat_1(A_73,B_71))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_435,plain,(
    ! [A_144,B_145,B_146] :
      ( r2_hidden('#skF_6'(k7_relat_1(A_144,B_145),B_146),B_145)
      | ~ v1_relat_1(A_144)
      | r1_tarski(k7_relat_1(A_144,B_145),B_146)
      | ~ v1_relat_1(k7_relat_1(A_144,B_145)) ) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_963,plain,(
    ! [A_242,B_243,B_244,B_245] :
      ( r2_hidden('#skF_6'(k7_relat_1(A_242,B_243),B_244),B_245)
      | ~ r1_tarski(B_243,B_245)
      | ~ v1_relat_1(A_242)
      | r1_tarski(k7_relat_1(A_242,B_243),B_244)
      | ~ v1_relat_1(k7_relat_1(A_242,B_243)) ) ),
    inference(resolution,[status(thm)],[c_435,c_2])).

tff(c_1733,plain,(
    ! [A_369,B_372,B_370,B_371,B_373] :
      ( r2_hidden('#skF_6'(k7_relat_1(A_369,B_371),B_372),B_373)
      | ~ r1_tarski(B_370,B_373)
      | ~ r1_tarski(B_371,B_370)
      | ~ v1_relat_1(A_369)
      | r1_tarski(k7_relat_1(A_369,B_371),B_372)
      | ~ v1_relat_1(k7_relat_1(A_369,B_371)) ) ),
    inference(resolution,[status(thm)],[c_963,c_2])).

tff(c_1775,plain,(
    ! [A_369,B_371,B_372] :
      ( r2_hidden('#skF_6'(k7_relat_1(A_369,B_371),B_372),'#skF_9')
      | ~ r1_tarski(B_371,'#skF_8')
      | ~ v1_relat_1(A_369)
      | r1_tarski(k7_relat_1(A_369,B_371),B_372)
      | ~ v1_relat_1(k7_relat_1(A_369,B_371)) ) ),
    inference(resolution,[status(thm)],[c_38,c_1733])).

tff(c_40,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(k4_tarski('#skF_6'(A_62,B_63),'#skF_7'(A_62,B_63)),A_62)
      | r1_tarski(A_62,B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_251,plain,(
    ! [A_111,B_112,B_113] :
      ( r2_hidden(k4_tarski('#skF_6'(A_111,B_112),'#skF_7'(A_111,B_112)),B_113)
      | ~ r1_tarski(A_111,B_113)
      | r1_tarski(A_111,B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_535,plain,(
    ! [A_179,B_180,B_181,B_182] :
      ( r2_hidden(k4_tarski('#skF_6'(A_179,B_180),'#skF_7'(A_179,B_180)),B_181)
      | ~ r1_tarski(B_182,B_181)
      | ~ r1_tarski(A_179,B_182)
      | r1_tarski(A_179,B_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_561,plain,(
    ! [A_179,B_180] :
      ( r2_hidden(k4_tarski('#skF_6'(A_179,B_180),'#skF_7'(A_179,B_180)),'#skF_11')
      | ~ r1_tarski(A_179,'#skF_10')
      | r1_tarski(A_179,B_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_40,c_535])).

tff(c_216,plain,(
    ! [D_100,E_101,A_102,B_103] :
      ( r2_hidden(k4_tarski(D_100,E_101),k7_relat_1(A_102,B_103))
      | ~ r2_hidden(k4_tarski(D_100,E_101),A_102)
      | ~ r2_hidden(D_100,B_103)
      | ~ v1_relat_1(k7_relat_1(A_102,B_103))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_25,B_35] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_25,B_35),'#skF_7'(A_25,B_35)),B_35)
      | r1_tarski(A_25,B_35)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3061,plain,(
    ! [A_559,A_560,B_561] :
      ( r1_tarski(A_559,k7_relat_1(A_560,B_561))
      | ~ v1_relat_1(A_559)
      | ~ r2_hidden(k4_tarski('#skF_6'(A_559,k7_relat_1(A_560,B_561)),'#skF_7'(A_559,k7_relat_1(A_560,B_561))),A_560)
      | ~ r2_hidden('#skF_6'(A_559,k7_relat_1(A_560,B_561)),B_561)
      | ~ v1_relat_1(k7_relat_1(A_560,B_561))
      | ~ v1_relat_1(A_560) ) ),
    inference(resolution,[status(thm)],[c_216,c_28])).

tff(c_3081,plain,(
    ! [A_179,B_561] :
      ( ~ r2_hidden('#skF_6'(A_179,k7_relat_1('#skF_11',B_561)),B_561)
      | ~ v1_relat_1(k7_relat_1('#skF_11',B_561))
      | ~ v1_relat_1('#skF_11')
      | ~ r1_tarski(A_179,'#skF_10')
      | r1_tarski(A_179,k7_relat_1('#skF_11',B_561))
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_561,c_3061])).

tff(c_3277,plain,(
    ! [A_566,B_567] :
      ( ~ r2_hidden('#skF_6'(A_566,k7_relat_1('#skF_11',B_567)),B_567)
      | ~ v1_relat_1(k7_relat_1('#skF_11',B_567))
      | ~ r1_tarski(A_566,'#skF_10')
      | r1_tarski(A_566,k7_relat_1('#skF_11',B_567))
      | ~ v1_relat_1(A_566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3081])).

tff(c_3304,plain,(
    ! [A_369,B_371] :
      ( ~ v1_relat_1(k7_relat_1('#skF_11','#skF_9'))
      | ~ r1_tarski(k7_relat_1(A_369,B_371),'#skF_10')
      | ~ r1_tarski(B_371,'#skF_8')
      | ~ v1_relat_1(A_369)
      | r1_tarski(k7_relat_1(A_369,B_371),k7_relat_1('#skF_11','#skF_9'))
      | ~ v1_relat_1(k7_relat_1(A_369,B_371)) ) ),
    inference(resolution,[status(thm)],[c_1775,c_3277])).

tff(c_6404,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_11','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_3304])).

tff(c_6407,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_6404])).

tff(c_6411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6407])).

tff(c_6413,plain,(
    v1_relat_1(k7_relat_1('#skF_11','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3304])).

tff(c_71,plain,(
    ! [A_62,B_63,B_2] :
      ( r2_hidden(k4_tarski('#skF_6'(A_62,B_63),'#skF_7'(A_62,B_63)),B_2)
      | ~ r1_tarski(A_62,B_2)
      | r1_tarski(A_62,B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_4477,plain,(
    ! [A_614,B_615,B_616] :
      ( ~ r2_hidden('#skF_6'(A_614,k7_relat_1(B_615,B_616)),B_616)
      | ~ v1_relat_1(k7_relat_1(B_615,B_616))
      | ~ v1_relat_1(B_615)
      | ~ r1_tarski(A_614,B_615)
      | r1_tarski(A_614,k7_relat_1(B_615,B_616))
      | ~ v1_relat_1(A_614) ) ),
    inference(resolution,[status(thm)],[c_71,c_3061])).

tff(c_8281,plain,(
    ! [B_666,A_667,B_668] :
      ( ~ v1_relat_1(k7_relat_1(B_666,'#skF_9'))
      | ~ v1_relat_1(B_666)
      | ~ r1_tarski(k7_relat_1(A_667,B_668),B_666)
      | ~ r1_tarski(B_668,'#skF_8')
      | ~ v1_relat_1(A_667)
      | r1_tarski(k7_relat_1(A_667,B_668),k7_relat_1(B_666,'#skF_9'))
      | ~ v1_relat_1(k7_relat_1(A_667,B_668)) ) ),
    inference(resolution,[status(thm)],[c_1775,c_4477])).

tff(c_36,plain,(
    ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),k7_relat_1('#skF_11','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8392,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_11','#skF_9'))
    | ~ v1_relat_1('#skF_11')
    | ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),'#skF_11')
    | ~ r1_tarski('#skF_8','#skF_8')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(resolution,[status(thm)],[c_8281,c_36])).

tff(c_8469,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),'#skF_11')
    | ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_53,c_42,c_6413,c_8392])).

tff(c_9499,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_8469])).

tff(c_9697,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_9499])).

tff(c_9701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9697])).

tff(c_9703,plain,(
    v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_8469])).

tff(c_97,plain,(
    ! [A_73,B_71,B_35] :
      ( r2_hidden('#skF_6'(k7_relat_1(A_73,B_71),B_35),B_71)
      | ~ v1_relat_1(A_73)
      | r1_tarski(k7_relat_1(A_73,B_71),B_35)
      | ~ v1_relat_1(k7_relat_1(A_73,B_71)) ) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_3104,plain,(
    ! [A_562,B_563] :
      ( ~ r2_hidden('#skF_6'(A_562,k7_relat_1(A_562,B_563)),B_563)
      | ~ v1_relat_1(k7_relat_1(A_562,B_563))
      | r1_tarski(A_562,k7_relat_1(A_562,B_563))
      | ~ v1_relat_1(A_562) ) ),
    inference(resolution,[status(thm)],[c_30,c_3061])).

tff(c_3135,plain,(
    ! [A_564,B_565] :
      ( ~ v1_relat_1(k7_relat_1(k7_relat_1(A_564,B_565),B_565))
      | ~ v1_relat_1(A_564)
      | r1_tarski(k7_relat_1(A_564,B_565),k7_relat_1(k7_relat_1(A_564,B_565),B_565))
      | ~ v1_relat_1(k7_relat_1(A_564,B_565)) ) ),
    inference(resolution,[status(thm)],[c_97,c_3104])).

tff(c_34,plain,(
    ! [B_45,A_44] :
      ( r1_tarski(k7_relat_1(B_45,A_44),B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    ! [C_55,B_56,A_57] :
      ( r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_59,B_60,B_61] :
      ( r2_hidden('#skF_1'(A_59,B_60),B_61)
      | ~ r1_tarski(A_59,B_61)
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_79,plain,(
    ! [A_66,B_67,B_68,B_69] :
      ( r2_hidden('#skF_1'(A_66,B_67),B_68)
      | ~ r1_tarski(B_69,B_68)
      | ~ r1_tarski(A_66,B_69)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_233,plain,(
    ! [A_104,B_105,B_106,A_107] :
      ( r2_hidden('#skF_1'(A_104,B_105),B_106)
      | ~ r1_tarski(A_104,k7_relat_1(B_106,A_107))
      | r1_tarski(A_104,B_105)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_242,plain,(
    ! [B_108,A_109,B_110] :
      ( r2_hidden('#skF_1'(k7_relat_1(B_108,A_109),B_110),B_108)
      | r1_tarski(k7_relat_1(B_108,A_109),B_110)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_53,c_233])).

tff(c_308,plain,(
    ! [B_122,A_123,B_124,B_125] :
      ( r2_hidden('#skF_1'(k7_relat_1(B_122,A_123),B_124),B_125)
      | ~ r1_tarski(B_122,B_125)
      | r1_tarski(k7_relat_1(B_122,A_123),B_124)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_242,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_317,plain,(
    ! [B_126,B_127,A_128] :
      ( ~ r1_tarski(B_126,B_127)
      | r1_tarski(k7_relat_1(B_126,A_128),B_127)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_308,c_4])).

tff(c_98,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),'#skF_11')
      | ~ r1_tarski(A_74,'#skF_10')
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_107,plain,(
    ! [A_76] :
      ( ~ r1_tarski(A_76,'#skF_10')
      | r1_tarski(A_76,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_66,plain,(
    ! [A_59,B_60,B_2,B_61] :
      ( r2_hidden('#skF_1'(A_59,B_60),B_2)
      | ~ r1_tarski(B_61,B_2)
      | ~ r1_tarski(A_59,B_61)
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_110,plain,(
    ! [A_59,B_60,A_76] :
      ( r2_hidden('#skF_1'(A_59,B_60),'#skF_11')
      | ~ r1_tarski(A_59,A_76)
      | r1_tarski(A_59,B_60)
      | ~ r1_tarski(A_76,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_107,c_66])).

tff(c_494,plain,(
    ! [B_167,A_168,B_169,B_170] :
      ( r2_hidden('#skF_1'(k7_relat_1(B_167,A_168),B_169),'#skF_11')
      | r1_tarski(k7_relat_1(B_167,A_168),B_169)
      | ~ r1_tarski(B_170,'#skF_10')
      | ~ r1_tarski(B_167,B_170)
      | ~ v1_relat_1(B_167) ) ),
    inference(resolution,[status(thm)],[c_317,c_110])).

tff(c_503,plain,(
    ! [B_167,A_168,B_169,A_44] :
      ( r2_hidden('#skF_1'(k7_relat_1(B_167,A_168),B_169),'#skF_11')
      | r1_tarski(k7_relat_1(B_167,A_168),B_169)
      | ~ r1_tarski(B_167,k7_relat_1('#skF_10',A_44))
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_494])).

tff(c_522,plain,(
    ! [B_175,A_176,B_177,A_178] :
      ( r2_hidden('#skF_1'(k7_relat_1(B_175,A_176),B_177),'#skF_11')
      | r1_tarski(k7_relat_1(B_175,A_176),B_177)
      | ~ r1_tarski(B_175,k7_relat_1('#skF_10',A_178))
      | ~ v1_relat_1(B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_503])).

tff(c_899,plain,(
    ! [A_230,A_231,B_232] :
      ( r2_hidden('#skF_1'(k7_relat_1(k7_relat_1('#skF_10',A_230),A_231),B_232),'#skF_11')
      | r1_tarski(k7_relat_1(k7_relat_1('#skF_10',A_230),A_231),B_232)
      | ~ v1_relat_1(k7_relat_1('#skF_10',A_230)) ) ),
    inference(resolution,[status(thm)],[c_53,c_522])).

tff(c_908,plain,(
    ! [A_233,A_234] :
      ( r1_tarski(k7_relat_1(k7_relat_1('#skF_10',A_233),A_234),'#skF_11')
      | ~ v1_relat_1(k7_relat_1('#skF_10',A_233)) ) ),
    inference(resolution,[status(thm)],[c_899,c_4])).

tff(c_935,plain,(
    ! [A_59,B_60,A_233,A_234] :
      ( r2_hidden('#skF_1'(A_59,B_60),'#skF_11')
      | ~ r1_tarski(A_59,k7_relat_1(k7_relat_1('#skF_10',A_233),A_234))
      | r1_tarski(A_59,B_60)
      | ~ v1_relat_1(k7_relat_1('#skF_10',A_233)) ) ),
    inference(resolution,[status(thm)],[c_908,c_66])).

tff(c_3199,plain,(
    ! [B_565,B_60] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_10',B_565),B_60),'#skF_11')
      | r1_tarski(k7_relat_1('#skF_10',B_565),B_60)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_10',B_565),B_565))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1(k7_relat_1('#skF_10',B_565)) ) ),
    inference(resolution,[status(thm)],[c_3135,c_935])).

tff(c_3588,plain,(
    ! [B_572,B_573] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_10',B_572),B_573),'#skF_11')
      | r1_tarski(k7_relat_1('#skF_10',B_572),B_573)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_10',B_572),B_572))
      | ~ v1_relat_1(k7_relat_1('#skF_10',B_572)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3199])).

tff(c_3593,plain,(
    ! [B_574,B_575] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_10',B_574),B_575),'#skF_11')
      | r1_tarski(k7_relat_1('#skF_10',B_574),B_575)
      | ~ v1_relat_1(k7_relat_1('#skF_10',B_574)) ) ),
    inference(resolution,[status(thm)],[c_32,c_3588])).

tff(c_3880,plain,(
    ! [B_587,B_588,B_589] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_10',B_587),B_588),B_589)
      | ~ r1_tarski('#skF_11',B_589)
      | r1_tarski(k7_relat_1('#skF_10',B_587),B_588)
      | ~ v1_relat_1(k7_relat_1('#skF_10',B_587)) ) ),
    inference(resolution,[status(thm)],[c_3593,c_2])).

tff(c_3891,plain,(
    ! [B_589,B_587] :
      ( ~ r1_tarski('#skF_11',B_589)
      | r1_tarski(k7_relat_1('#skF_10',B_587),B_589)
      | ~ v1_relat_1(k7_relat_1('#skF_10',B_587)) ) ),
    inference(resolution,[status(thm)],[c_3880,c_4])).

tff(c_9702,plain,(
    ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_8469])).

tff(c_9711,plain,
    ( ~ r1_tarski('#skF_11','#skF_11')
    | ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3891,c_9702])).

tff(c_9733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9703,c_53,c_9711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.24/3.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/3.96  
% 11.24/3.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/3.96  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1
% 11.24/3.96  
% 11.24/3.96  %Foreground sorts:
% 11.24/3.96  
% 11.24/3.96  
% 11.24/3.96  %Background operators:
% 11.24/3.96  
% 11.24/3.96  
% 11.24/3.96  %Foreground operators:
% 11.24/3.96  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.24/3.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.24/3.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.24/3.96  tff('#skF_11', type, '#skF_11': $i).
% 11.24/3.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.24/3.96  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.24/3.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.24/3.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.24/3.96  tff('#skF_10', type, '#skF_10': $i).
% 11.24/3.96  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.24/3.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.24/3.96  tff('#skF_9', type, '#skF_9': $i).
% 11.24/3.96  tff('#skF_8', type, '#skF_8': $i).
% 11.24/3.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.24/3.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.24/3.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.24/3.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.24/3.96  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 11.24/3.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.24/3.96  
% 11.24/3.98  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 11.24/3.98  tff(f_60, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 11.24/3.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.24/3.98  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 11.24/3.98  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 11.24/3.98  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 11.24/3.98  tff(c_44, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.24/3.98  tff(c_32, plain, (![A_42, B_43]: (v1_relat_1(k7_relat_1(A_42, B_43)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.24/3.98  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/3.98  tff(c_48, plain, (![A_53, B_54]: (~r2_hidden('#skF_1'(A_53, B_54), B_54) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/3.98  tff(c_53, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_48])).
% 11.24/3.98  tff(c_42, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.24/3.98  tff(c_38, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.24/3.98  tff(c_30, plain, (![A_25, B_35]: (r2_hidden(k4_tarski('#skF_6'(A_25, B_35), '#skF_7'(A_25, B_35)), A_25) | r1_tarski(A_25, B_35) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.24/3.98  tff(c_92, plain, (![D_70, B_71, E_72, A_73]: (r2_hidden(D_70, B_71) | ~r2_hidden(k4_tarski(D_70, E_72), k7_relat_1(A_73, B_71)) | ~v1_relat_1(k7_relat_1(A_73, B_71)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.24/3.98  tff(c_435, plain, (![A_144, B_145, B_146]: (r2_hidden('#skF_6'(k7_relat_1(A_144, B_145), B_146), B_145) | ~v1_relat_1(A_144) | r1_tarski(k7_relat_1(A_144, B_145), B_146) | ~v1_relat_1(k7_relat_1(A_144, B_145)))), inference(resolution, [status(thm)], [c_30, c_92])).
% 11.24/3.98  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/3.98  tff(c_963, plain, (![A_242, B_243, B_244, B_245]: (r2_hidden('#skF_6'(k7_relat_1(A_242, B_243), B_244), B_245) | ~r1_tarski(B_243, B_245) | ~v1_relat_1(A_242) | r1_tarski(k7_relat_1(A_242, B_243), B_244) | ~v1_relat_1(k7_relat_1(A_242, B_243)))), inference(resolution, [status(thm)], [c_435, c_2])).
% 11.24/3.98  tff(c_1733, plain, (![A_369, B_372, B_370, B_371, B_373]: (r2_hidden('#skF_6'(k7_relat_1(A_369, B_371), B_372), B_373) | ~r1_tarski(B_370, B_373) | ~r1_tarski(B_371, B_370) | ~v1_relat_1(A_369) | r1_tarski(k7_relat_1(A_369, B_371), B_372) | ~v1_relat_1(k7_relat_1(A_369, B_371)))), inference(resolution, [status(thm)], [c_963, c_2])).
% 11.24/3.98  tff(c_1775, plain, (![A_369, B_371, B_372]: (r2_hidden('#skF_6'(k7_relat_1(A_369, B_371), B_372), '#skF_9') | ~r1_tarski(B_371, '#skF_8') | ~v1_relat_1(A_369) | r1_tarski(k7_relat_1(A_369, B_371), B_372) | ~v1_relat_1(k7_relat_1(A_369, B_371)))), inference(resolution, [status(thm)], [c_38, c_1733])).
% 11.24/3.98  tff(c_40, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.24/3.98  tff(c_68, plain, (![A_62, B_63]: (r2_hidden(k4_tarski('#skF_6'(A_62, B_63), '#skF_7'(A_62, B_63)), A_62) | r1_tarski(A_62, B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.24/3.98  tff(c_251, plain, (![A_111, B_112, B_113]: (r2_hidden(k4_tarski('#skF_6'(A_111, B_112), '#skF_7'(A_111, B_112)), B_113) | ~r1_tarski(A_111, B_113) | r1_tarski(A_111, B_112) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_68, c_2])).
% 11.24/3.98  tff(c_535, plain, (![A_179, B_180, B_181, B_182]: (r2_hidden(k4_tarski('#skF_6'(A_179, B_180), '#skF_7'(A_179, B_180)), B_181) | ~r1_tarski(B_182, B_181) | ~r1_tarski(A_179, B_182) | r1_tarski(A_179, B_180) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_251, c_2])).
% 11.24/3.98  tff(c_561, plain, (![A_179, B_180]: (r2_hidden(k4_tarski('#skF_6'(A_179, B_180), '#skF_7'(A_179, B_180)), '#skF_11') | ~r1_tarski(A_179, '#skF_10') | r1_tarski(A_179, B_180) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_40, c_535])).
% 11.24/3.98  tff(c_216, plain, (![D_100, E_101, A_102, B_103]: (r2_hidden(k4_tarski(D_100, E_101), k7_relat_1(A_102, B_103)) | ~r2_hidden(k4_tarski(D_100, E_101), A_102) | ~r2_hidden(D_100, B_103) | ~v1_relat_1(k7_relat_1(A_102, B_103)) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.24/3.98  tff(c_28, plain, (![A_25, B_35]: (~r2_hidden(k4_tarski('#skF_6'(A_25, B_35), '#skF_7'(A_25, B_35)), B_35) | r1_tarski(A_25, B_35) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.24/3.98  tff(c_3061, plain, (![A_559, A_560, B_561]: (r1_tarski(A_559, k7_relat_1(A_560, B_561)) | ~v1_relat_1(A_559) | ~r2_hidden(k4_tarski('#skF_6'(A_559, k7_relat_1(A_560, B_561)), '#skF_7'(A_559, k7_relat_1(A_560, B_561))), A_560) | ~r2_hidden('#skF_6'(A_559, k7_relat_1(A_560, B_561)), B_561) | ~v1_relat_1(k7_relat_1(A_560, B_561)) | ~v1_relat_1(A_560))), inference(resolution, [status(thm)], [c_216, c_28])).
% 11.24/3.98  tff(c_3081, plain, (![A_179, B_561]: (~r2_hidden('#skF_6'(A_179, k7_relat_1('#skF_11', B_561)), B_561) | ~v1_relat_1(k7_relat_1('#skF_11', B_561)) | ~v1_relat_1('#skF_11') | ~r1_tarski(A_179, '#skF_10') | r1_tarski(A_179, k7_relat_1('#skF_11', B_561)) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_561, c_3061])).
% 11.24/3.98  tff(c_3277, plain, (![A_566, B_567]: (~r2_hidden('#skF_6'(A_566, k7_relat_1('#skF_11', B_567)), B_567) | ~v1_relat_1(k7_relat_1('#skF_11', B_567)) | ~r1_tarski(A_566, '#skF_10') | r1_tarski(A_566, k7_relat_1('#skF_11', B_567)) | ~v1_relat_1(A_566))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3081])).
% 11.24/3.98  tff(c_3304, plain, (![A_369, B_371]: (~v1_relat_1(k7_relat_1('#skF_11', '#skF_9')) | ~r1_tarski(k7_relat_1(A_369, B_371), '#skF_10') | ~r1_tarski(B_371, '#skF_8') | ~v1_relat_1(A_369) | r1_tarski(k7_relat_1(A_369, B_371), k7_relat_1('#skF_11', '#skF_9')) | ~v1_relat_1(k7_relat_1(A_369, B_371)))), inference(resolution, [status(thm)], [c_1775, c_3277])).
% 11.24/3.98  tff(c_6404, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_9'))), inference(splitLeft, [status(thm)], [c_3304])).
% 11.24/3.98  tff(c_6407, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_6404])).
% 11.24/3.98  tff(c_6411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6407])).
% 11.24/3.98  tff(c_6413, plain, (v1_relat_1(k7_relat_1('#skF_11', '#skF_9'))), inference(splitRight, [status(thm)], [c_3304])).
% 11.24/3.98  tff(c_71, plain, (![A_62, B_63, B_2]: (r2_hidden(k4_tarski('#skF_6'(A_62, B_63), '#skF_7'(A_62, B_63)), B_2) | ~r1_tarski(A_62, B_2) | r1_tarski(A_62, B_63) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_68, c_2])).
% 11.24/3.98  tff(c_4477, plain, (![A_614, B_615, B_616]: (~r2_hidden('#skF_6'(A_614, k7_relat_1(B_615, B_616)), B_616) | ~v1_relat_1(k7_relat_1(B_615, B_616)) | ~v1_relat_1(B_615) | ~r1_tarski(A_614, B_615) | r1_tarski(A_614, k7_relat_1(B_615, B_616)) | ~v1_relat_1(A_614))), inference(resolution, [status(thm)], [c_71, c_3061])).
% 11.24/3.98  tff(c_8281, plain, (![B_666, A_667, B_668]: (~v1_relat_1(k7_relat_1(B_666, '#skF_9')) | ~v1_relat_1(B_666) | ~r1_tarski(k7_relat_1(A_667, B_668), B_666) | ~r1_tarski(B_668, '#skF_8') | ~v1_relat_1(A_667) | r1_tarski(k7_relat_1(A_667, B_668), k7_relat_1(B_666, '#skF_9')) | ~v1_relat_1(k7_relat_1(A_667, B_668)))), inference(resolution, [status(thm)], [c_1775, c_4477])).
% 11.24/3.98  tff(c_36, plain, (~r1_tarski(k7_relat_1('#skF_10', '#skF_8'), k7_relat_1('#skF_11', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.24/3.98  tff(c_8392, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_9')) | ~v1_relat_1('#skF_11') | ~r1_tarski(k7_relat_1('#skF_10', '#skF_8'), '#skF_11') | ~r1_tarski('#skF_8', '#skF_8') | ~v1_relat_1('#skF_10') | ~v1_relat_1(k7_relat_1('#skF_10', '#skF_8'))), inference(resolution, [status(thm)], [c_8281, c_36])).
% 11.24/3.98  tff(c_8469, plain, (~r1_tarski(k7_relat_1('#skF_10', '#skF_8'), '#skF_11') | ~v1_relat_1(k7_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_53, c_42, c_6413, c_8392])).
% 11.24/3.98  tff(c_9499, plain, (~v1_relat_1(k7_relat_1('#skF_10', '#skF_8'))), inference(splitLeft, [status(thm)], [c_8469])).
% 11.24/3.98  tff(c_9697, plain, (~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_9499])).
% 11.24/3.98  tff(c_9701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_9697])).
% 11.24/3.98  tff(c_9703, plain, (v1_relat_1(k7_relat_1('#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_8469])).
% 11.24/3.98  tff(c_97, plain, (![A_73, B_71, B_35]: (r2_hidden('#skF_6'(k7_relat_1(A_73, B_71), B_35), B_71) | ~v1_relat_1(A_73) | r1_tarski(k7_relat_1(A_73, B_71), B_35) | ~v1_relat_1(k7_relat_1(A_73, B_71)))), inference(resolution, [status(thm)], [c_30, c_92])).
% 11.24/3.98  tff(c_3104, plain, (![A_562, B_563]: (~r2_hidden('#skF_6'(A_562, k7_relat_1(A_562, B_563)), B_563) | ~v1_relat_1(k7_relat_1(A_562, B_563)) | r1_tarski(A_562, k7_relat_1(A_562, B_563)) | ~v1_relat_1(A_562))), inference(resolution, [status(thm)], [c_30, c_3061])).
% 11.24/3.98  tff(c_3135, plain, (![A_564, B_565]: (~v1_relat_1(k7_relat_1(k7_relat_1(A_564, B_565), B_565)) | ~v1_relat_1(A_564) | r1_tarski(k7_relat_1(A_564, B_565), k7_relat_1(k7_relat_1(A_564, B_565), B_565)) | ~v1_relat_1(k7_relat_1(A_564, B_565)))), inference(resolution, [status(thm)], [c_97, c_3104])).
% 11.24/3.98  tff(c_34, plain, (![B_45, A_44]: (r1_tarski(k7_relat_1(B_45, A_44), B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.24/3.98  tff(c_54, plain, (![C_55, B_56, A_57]: (r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/3.98  tff(c_59, plain, (![A_59, B_60, B_61]: (r2_hidden('#skF_1'(A_59, B_60), B_61) | ~r1_tarski(A_59, B_61) | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_6, c_54])).
% 11.24/3.98  tff(c_79, plain, (![A_66, B_67, B_68, B_69]: (r2_hidden('#skF_1'(A_66, B_67), B_68) | ~r1_tarski(B_69, B_68) | ~r1_tarski(A_66, B_69) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_59, c_2])).
% 11.24/3.98  tff(c_233, plain, (![A_104, B_105, B_106, A_107]: (r2_hidden('#skF_1'(A_104, B_105), B_106) | ~r1_tarski(A_104, k7_relat_1(B_106, A_107)) | r1_tarski(A_104, B_105) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_34, c_79])).
% 11.24/3.98  tff(c_242, plain, (![B_108, A_109, B_110]: (r2_hidden('#skF_1'(k7_relat_1(B_108, A_109), B_110), B_108) | r1_tarski(k7_relat_1(B_108, A_109), B_110) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_53, c_233])).
% 11.24/3.98  tff(c_308, plain, (![B_122, A_123, B_124, B_125]: (r2_hidden('#skF_1'(k7_relat_1(B_122, A_123), B_124), B_125) | ~r1_tarski(B_122, B_125) | r1_tarski(k7_relat_1(B_122, A_123), B_124) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_242, c_2])).
% 11.24/3.98  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/3.98  tff(c_317, plain, (![B_126, B_127, A_128]: (~r1_tarski(B_126, B_127) | r1_tarski(k7_relat_1(B_126, A_128), B_127) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_308, c_4])).
% 11.24/3.98  tff(c_98, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), '#skF_11') | ~r1_tarski(A_74, '#skF_10') | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_40, c_79])).
% 11.24/3.98  tff(c_107, plain, (![A_76]: (~r1_tarski(A_76, '#skF_10') | r1_tarski(A_76, '#skF_11'))), inference(resolution, [status(thm)], [c_98, c_4])).
% 11.24/3.98  tff(c_66, plain, (![A_59, B_60, B_2, B_61]: (r2_hidden('#skF_1'(A_59, B_60), B_2) | ~r1_tarski(B_61, B_2) | ~r1_tarski(A_59, B_61) | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_59, c_2])).
% 11.24/3.98  tff(c_110, plain, (![A_59, B_60, A_76]: (r2_hidden('#skF_1'(A_59, B_60), '#skF_11') | ~r1_tarski(A_59, A_76) | r1_tarski(A_59, B_60) | ~r1_tarski(A_76, '#skF_10'))), inference(resolution, [status(thm)], [c_107, c_66])).
% 11.24/3.98  tff(c_494, plain, (![B_167, A_168, B_169, B_170]: (r2_hidden('#skF_1'(k7_relat_1(B_167, A_168), B_169), '#skF_11') | r1_tarski(k7_relat_1(B_167, A_168), B_169) | ~r1_tarski(B_170, '#skF_10') | ~r1_tarski(B_167, B_170) | ~v1_relat_1(B_167))), inference(resolution, [status(thm)], [c_317, c_110])).
% 11.24/3.98  tff(c_503, plain, (![B_167, A_168, B_169, A_44]: (r2_hidden('#skF_1'(k7_relat_1(B_167, A_168), B_169), '#skF_11') | r1_tarski(k7_relat_1(B_167, A_168), B_169) | ~r1_tarski(B_167, k7_relat_1('#skF_10', A_44)) | ~v1_relat_1(B_167) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_494])).
% 11.24/3.98  tff(c_522, plain, (![B_175, A_176, B_177, A_178]: (r2_hidden('#skF_1'(k7_relat_1(B_175, A_176), B_177), '#skF_11') | r1_tarski(k7_relat_1(B_175, A_176), B_177) | ~r1_tarski(B_175, k7_relat_1('#skF_10', A_178)) | ~v1_relat_1(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_503])).
% 11.24/3.98  tff(c_899, plain, (![A_230, A_231, B_232]: (r2_hidden('#skF_1'(k7_relat_1(k7_relat_1('#skF_10', A_230), A_231), B_232), '#skF_11') | r1_tarski(k7_relat_1(k7_relat_1('#skF_10', A_230), A_231), B_232) | ~v1_relat_1(k7_relat_1('#skF_10', A_230)))), inference(resolution, [status(thm)], [c_53, c_522])).
% 11.24/3.98  tff(c_908, plain, (![A_233, A_234]: (r1_tarski(k7_relat_1(k7_relat_1('#skF_10', A_233), A_234), '#skF_11') | ~v1_relat_1(k7_relat_1('#skF_10', A_233)))), inference(resolution, [status(thm)], [c_899, c_4])).
% 11.24/3.98  tff(c_935, plain, (![A_59, B_60, A_233, A_234]: (r2_hidden('#skF_1'(A_59, B_60), '#skF_11') | ~r1_tarski(A_59, k7_relat_1(k7_relat_1('#skF_10', A_233), A_234)) | r1_tarski(A_59, B_60) | ~v1_relat_1(k7_relat_1('#skF_10', A_233)))), inference(resolution, [status(thm)], [c_908, c_66])).
% 11.24/3.98  tff(c_3199, plain, (![B_565, B_60]: (r2_hidden('#skF_1'(k7_relat_1('#skF_10', B_565), B_60), '#skF_11') | r1_tarski(k7_relat_1('#skF_10', B_565), B_60) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_10', B_565), B_565)) | ~v1_relat_1('#skF_10') | ~v1_relat_1(k7_relat_1('#skF_10', B_565)))), inference(resolution, [status(thm)], [c_3135, c_935])).
% 11.24/3.98  tff(c_3588, plain, (![B_572, B_573]: (r2_hidden('#skF_1'(k7_relat_1('#skF_10', B_572), B_573), '#skF_11') | r1_tarski(k7_relat_1('#skF_10', B_572), B_573) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_10', B_572), B_572)) | ~v1_relat_1(k7_relat_1('#skF_10', B_572)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3199])).
% 11.24/3.98  tff(c_3593, plain, (![B_574, B_575]: (r2_hidden('#skF_1'(k7_relat_1('#skF_10', B_574), B_575), '#skF_11') | r1_tarski(k7_relat_1('#skF_10', B_574), B_575) | ~v1_relat_1(k7_relat_1('#skF_10', B_574)))), inference(resolution, [status(thm)], [c_32, c_3588])).
% 11.24/3.98  tff(c_3880, plain, (![B_587, B_588, B_589]: (r2_hidden('#skF_1'(k7_relat_1('#skF_10', B_587), B_588), B_589) | ~r1_tarski('#skF_11', B_589) | r1_tarski(k7_relat_1('#skF_10', B_587), B_588) | ~v1_relat_1(k7_relat_1('#skF_10', B_587)))), inference(resolution, [status(thm)], [c_3593, c_2])).
% 11.24/3.98  tff(c_3891, plain, (![B_589, B_587]: (~r1_tarski('#skF_11', B_589) | r1_tarski(k7_relat_1('#skF_10', B_587), B_589) | ~v1_relat_1(k7_relat_1('#skF_10', B_587)))), inference(resolution, [status(thm)], [c_3880, c_4])).
% 11.24/3.98  tff(c_9702, plain, (~r1_tarski(k7_relat_1('#skF_10', '#skF_8'), '#skF_11')), inference(splitRight, [status(thm)], [c_8469])).
% 11.24/3.98  tff(c_9711, plain, (~r1_tarski('#skF_11', '#skF_11') | ~v1_relat_1(k7_relat_1('#skF_10', '#skF_8'))), inference(resolution, [status(thm)], [c_3891, c_9702])).
% 11.24/3.98  tff(c_9733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9703, c_53, c_9711])).
% 11.24/3.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/3.98  
% 11.24/3.98  Inference rules
% 11.24/3.98  ----------------------
% 11.24/3.98  #Ref     : 0
% 11.24/3.98  #Sup     : 2424
% 11.24/3.98  #Fact    : 0
% 11.24/3.98  #Define  : 0
% 11.24/3.98  #Split   : 18
% 11.24/3.98  #Chain   : 0
% 11.24/3.98  #Close   : 0
% 11.24/3.98  
% 11.24/3.98  Ordering : KBO
% 11.24/3.98  
% 11.24/3.98  Simplification rules
% 11.24/3.98  ----------------------
% 11.24/3.98  #Subsume      : 924
% 11.24/3.98  #Demod        : 2040
% 11.24/3.98  #Tautology    : 75
% 11.24/3.98  #SimpNegUnit  : 0
% 11.24/3.98  #BackRed      : 0
% 11.24/3.98  
% 11.24/3.98  #Partial instantiations: 0
% 11.24/3.98  #Strategies tried      : 1
% 11.24/3.98  
% 11.24/3.98  Timing (in seconds)
% 11.24/3.98  ----------------------
% 11.24/3.98  Preprocessing        : 0.31
% 11.24/3.98  Parsing              : 0.17
% 11.24/3.98  CNF conversion       : 0.03
% 11.24/3.98  Main loop            : 2.82
% 11.24/3.98  Inferencing          : 0.60
% 11.24/3.99  Reduction            : 0.63
% 11.24/3.99  Demodulation         : 0.41
% 11.24/3.99  BG Simplification    : 0.07
% 11.24/3.99  Subsumption          : 1.39
% 11.24/3.99  Abstraction          : 0.09
% 11.24/3.99  MUC search           : 0.00
% 11.24/3.99  Cooper               : 0.00
% 11.24/3.99  Total                : 3.17
% 11.24/3.99  Index Insertion      : 0.00
% 11.24/3.99  Index Deletion       : 0.00
% 11.24/3.99  Index Matching       : 0.00
% 11.24/3.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
