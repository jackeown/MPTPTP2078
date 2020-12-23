%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0477+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:22 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 917 expanded)
%              Number of leaves         :   21 ( 318 expanded)
%              Depth                    :   19
%              Number of atoms          :  216 (2510 expanded)
%              Number of equality atoms :   92 ( 911 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k4_relat_1 > #skF_6 > #skF_3 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(c_32,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_231,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(k4_tarski('#skF_6'(A_72,B_73),'#skF_5'(A_72,B_73)),A_72)
      | r2_hidden(k4_tarski('#skF_7'(A_72,B_73),'#skF_8'(A_72,B_73)),B_73)
      | k4_relat_1(A_72) = B_73
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_243,plain,(
    ! [A_1,B_73] :
      ( '#skF_6'(k6_relat_1(A_1),B_73) = '#skF_5'(k6_relat_1(A_1),B_73)
      | r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_1),B_73),'#skF_8'(k6_relat_1(A_1),B_73)),B_73)
      | k4_relat_1(k6_relat_1(A_1)) = B_73
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_231,c_38])).

tff(c_345,plain,(
    ! [A_92,B_93] :
      ( '#skF_6'(k6_relat_1(A_92),B_93) = '#skF_5'(k6_relat_1(A_92),B_93)
      | r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_92),B_93),'#skF_8'(k6_relat_1(A_92),B_93)),B_93)
      | k4_relat_1(k6_relat_1(A_92)) = B_93
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_357,plain,(
    ! [A_92,A_1] :
      ( '#skF_8'(k6_relat_1(A_92),k6_relat_1(A_1)) = '#skF_7'(k6_relat_1(A_92),k6_relat_1(A_1))
      | '#skF_6'(k6_relat_1(A_92),k6_relat_1(A_1)) = '#skF_5'(k6_relat_1(A_92),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(k6_relat_1(A_92))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_345,c_38])).

tff(c_385,plain,(
    ! [A_96,A_97] :
      ( '#skF_8'(k6_relat_1(A_96),k6_relat_1(A_97)) = '#skF_7'(k6_relat_1(A_96),k6_relat_1(A_97))
      | '#skF_6'(k6_relat_1(A_96),k6_relat_1(A_97)) = '#skF_5'(k6_relat_1(A_96),k6_relat_1(A_97))
      | k6_relat_1(A_97) = k4_relat_1(k6_relat_1(A_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_357])).

tff(c_255,plain,(
    ! [A_72,A_1] :
      ( '#skF_8'(A_72,k6_relat_1(A_1)) = '#skF_7'(A_72,k6_relat_1(A_1))
      | r2_hidden(k4_tarski('#skF_6'(A_72,k6_relat_1(A_1)),'#skF_5'(A_72,k6_relat_1(A_1))),A_72)
      | k6_relat_1(A_1) = k4_relat_1(A_72)
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_231,c_38])).

tff(c_269,plain,(
    ! [A_72,A_1] :
      ( '#skF_8'(A_72,k6_relat_1(A_1)) = '#skF_7'(A_72,k6_relat_1(A_1))
      | r2_hidden(k4_tarski('#skF_6'(A_72,k6_relat_1(A_1)),'#skF_5'(A_72,k6_relat_1(A_1))),A_72)
      | k6_relat_1(A_1) = k4_relat_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_255])).

tff(c_391,plain,(
    ! [A_96,A_97] :
      ( '#skF_8'(k6_relat_1(A_96),k6_relat_1(A_97)) = '#skF_7'(k6_relat_1(A_96),k6_relat_1(A_97))
      | r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_96),k6_relat_1(A_97)),'#skF_5'(k6_relat_1(A_96),k6_relat_1(A_97))),k6_relat_1(A_96))
      | k6_relat_1(A_97) = k4_relat_1(k6_relat_1(A_96))
      | ~ v1_relat_1(k6_relat_1(A_96))
      | '#skF_8'(k6_relat_1(A_96),k6_relat_1(A_97)) = '#skF_7'(k6_relat_1(A_96),k6_relat_1(A_97))
      | k6_relat_1(A_97) = k4_relat_1(k6_relat_1(A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_269])).

tff(c_537,plain,(
    ! [A_126,A_127] :
      ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_126),k6_relat_1(A_127)),'#skF_5'(k6_relat_1(A_126),k6_relat_1(A_127))),k6_relat_1(A_126))
      | '#skF_8'(k6_relat_1(A_126),k6_relat_1(A_127)) = '#skF_7'(k6_relat_1(A_126),k6_relat_1(A_127))
      | k6_relat_1(A_127) = k4_relat_1(k6_relat_1(A_126)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_391])).

tff(c_364,plain,(
    ! [A_92,A_1] :
      ( '#skF_8'(k6_relat_1(A_92),k6_relat_1(A_1)) = '#skF_7'(k6_relat_1(A_92),k6_relat_1(A_1))
      | '#skF_6'(k6_relat_1(A_92),k6_relat_1(A_1)) = '#skF_5'(k6_relat_1(A_92),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(k6_relat_1(A_92)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_357])).

tff(c_318,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_86,B_87),'#skF_6'(A_86,B_87)),B_87)
      | r2_hidden(k4_tarski('#skF_7'(A_86,B_87),'#skF_8'(A_86,B_87)),B_87)
      | k4_relat_1(A_86) = B_87
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_330,plain,(
    ! [A_86,A_1] :
      ( '#skF_8'(A_86,k6_relat_1(A_1)) = '#skF_7'(A_86,k6_relat_1(A_1))
      | ~ r2_hidden(k4_tarski('#skF_5'(A_86,k6_relat_1(A_1)),'#skF_6'(A_86,k6_relat_1(A_1))),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(A_86)
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_318,c_38])).

tff(c_471,plain,(
    ! [A_106,A_107] :
      ( '#skF_8'(A_106,k6_relat_1(A_107)) = '#skF_7'(A_106,k6_relat_1(A_107))
      | ~ r2_hidden(k4_tarski('#skF_5'(A_106,k6_relat_1(A_107)),'#skF_6'(A_106,k6_relat_1(A_107))),k6_relat_1(A_107))
      | k6_relat_1(A_107) = k4_relat_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_330])).

tff(c_474,plain,(
    ! [A_92,A_1] :
      ( '#skF_8'(k6_relat_1(A_92),k6_relat_1(A_1)) = '#skF_7'(k6_relat_1(A_92),k6_relat_1(A_1))
      | ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_92),k6_relat_1(A_1)),'#skF_5'(k6_relat_1(A_92),k6_relat_1(A_1))),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(k6_relat_1(A_92))
      | ~ v1_relat_1(k6_relat_1(A_92))
      | '#skF_8'(k6_relat_1(A_92),k6_relat_1(A_1)) = '#skF_7'(k6_relat_1(A_92),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(k6_relat_1(A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_471])).

tff(c_476,plain,(
    ! [A_92,A_1] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_92),k6_relat_1(A_1)),'#skF_5'(k6_relat_1(A_92),k6_relat_1(A_1))),k6_relat_1(A_1))
      | '#skF_8'(k6_relat_1(A_92),k6_relat_1(A_1)) = '#skF_7'(k6_relat_1(A_92),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(k6_relat_1(A_92)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_474])).

tff(c_552,plain,(
    ! [A_128] :
      ( '#skF_8'(k6_relat_1(A_128),k6_relat_1(A_128)) = '#skF_7'(k6_relat_1(A_128),k6_relat_1(A_128))
      | k4_relat_1(k6_relat_1(A_128)) = k6_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_537,c_476])).

tff(c_262,plain,(
    ! [A_1,B_73] :
      ( '#skF_6'(k6_relat_1(A_1),B_73) = '#skF_5'(k6_relat_1(A_1),B_73)
      | r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_1),B_73),'#skF_8'(k6_relat_1(A_1),B_73)),B_73)
      | k4_relat_1(k6_relat_1(A_1)) = B_73
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_561,plain,(
    ! [A_128] :
      ( '#skF_6'(k6_relat_1(A_128),k6_relat_1(A_128)) = '#skF_5'(k6_relat_1(A_128),k6_relat_1(A_128))
      | r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_128),k6_relat_1(A_128)),'#skF_7'(k6_relat_1(A_128),k6_relat_1(A_128))),k6_relat_1(A_128))
      | k4_relat_1(k6_relat_1(A_128)) = k6_relat_1(A_128)
      | ~ v1_relat_1(k6_relat_1(A_128))
      | k4_relat_1(k6_relat_1(A_128)) = k6_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_262])).

tff(c_579,plain,(
    ! [A_128] :
      ( '#skF_6'(k6_relat_1(A_128),k6_relat_1(A_128)) = '#skF_5'(k6_relat_1(A_128),k6_relat_1(A_128))
      | r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_128),k6_relat_1(A_128)),'#skF_7'(k6_relat_1(A_128),k6_relat_1(A_128))),k6_relat_1(A_128))
      | k4_relat_1(k6_relat_1(A_128)) = k6_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_561])).

tff(c_209,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(k4_tarski('#skF_6'(A_66,B_67),'#skF_5'(A_66,B_67)),A_66)
      | ~ r2_hidden(k4_tarski('#skF_8'(A_66,B_67),'#skF_7'(A_66,B_67)),A_66)
      | k4_relat_1(A_66) = B_67
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_221,plain,(
    ! [A_1,B_67] :
      ( '#skF_6'(k6_relat_1(A_1),B_67) = '#skF_5'(k6_relat_1(A_1),B_67)
      | ~ r2_hidden(k4_tarski('#skF_8'(k6_relat_1(A_1),B_67),'#skF_7'(k6_relat_1(A_1),B_67)),k6_relat_1(A_1))
      | k4_relat_1(k6_relat_1(A_1)) = B_67
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_209,c_38])).

tff(c_228,plain,(
    ! [A_1,B_67] :
      ( '#skF_6'(k6_relat_1(A_1),B_67) = '#skF_5'(k6_relat_1(A_1),B_67)
      | ~ r2_hidden(k4_tarski('#skF_8'(k6_relat_1(A_1),B_67),'#skF_7'(k6_relat_1(A_1),B_67)),k6_relat_1(A_1))
      | k4_relat_1(k6_relat_1(A_1)) = B_67
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_221])).

tff(c_558,plain,(
    ! [A_128] :
      ( '#skF_6'(k6_relat_1(A_128),k6_relat_1(A_128)) = '#skF_5'(k6_relat_1(A_128),k6_relat_1(A_128))
      | ~ r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_128),k6_relat_1(A_128)),'#skF_7'(k6_relat_1(A_128),k6_relat_1(A_128))),k6_relat_1(A_128))
      | k4_relat_1(k6_relat_1(A_128)) = k6_relat_1(A_128)
      | ~ v1_relat_1(k6_relat_1(A_128))
      | k4_relat_1(k6_relat_1(A_128)) = k6_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_228])).

tff(c_713,plain,(
    ! [A_142] :
      ( '#skF_6'(k6_relat_1(A_142),k6_relat_1(A_142)) = '#skF_5'(k6_relat_1(A_142),k6_relat_1(A_142))
      | ~ r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_142),k6_relat_1(A_142)),'#skF_7'(k6_relat_1(A_142),k6_relat_1(A_142))),k6_relat_1(A_142))
      | k4_relat_1(k6_relat_1(A_142)) = k6_relat_1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_558])).

tff(c_723,plain,(
    ! [A_143] :
      ( '#skF_6'(k6_relat_1(A_143),k6_relat_1(A_143)) = '#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_579,c_713])).

tff(c_18,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_251,plain,(
    ! [A_72,A_1] :
      ( r2_hidden('#skF_7'(A_72,k6_relat_1(A_1)),A_1)
      | r2_hidden(k4_tarski('#skF_6'(A_72,k6_relat_1(A_1)),'#skF_5'(A_72,k6_relat_1(A_1))),A_72)
      | k6_relat_1(A_1) = k4_relat_1(A_72)
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_231,c_36])).

tff(c_266,plain,(
    ! [A_72,A_1] :
      ( r2_hidden('#skF_7'(A_72,k6_relat_1(A_1)),A_1)
      | r2_hidden(k4_tarski('#skF_6'(A_72,k6_relat_1(A_1)),'#skF_5'(A_72,k6_relat_1(A_1))),A_72)
      | k6_relat_1(A_1) = k4_relat_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_251])).

tff(c_744,plain,(
    ! [A_143] :
      ( r2_hidden('#skF_7'(k6_relat_1(A_143),k6_relat_1(A_143)),A_143)
      | r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143)),'#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143))),k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143)
      | ~ v1_relat_1(k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_266])).

tff(c_817,plain,(
    ! [A_151] :
      ( r2_hidden('#skF_7'(k6_relat_1(A_151),k6_relat_1(A_151)),A_151)
      | r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_151),k6_relat_1(A_151)),'#skF_5'(k6_relat_1(A_151),k6_relat_1(A_151))),k6_relat_1(A_151))
      | k4_relat_1(k6_relat_1(A_151)) = k6_relat_1(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_744])).

tff(c_326,plain,(
    ! [A_86,A_1] :
      ( r2_hidden('#skF_7'(A_86,k6_relat_1(A_1)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_86,k6_relat_1(A_1)),'#skF_6'(A_86,k6_relat_1(A_1))),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(A_86)
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_318,c_36])).

tff(c_334,plain,(
    ! [A_86,A_1] :
      ( r2_hidden('#skF_7'(A_86,k6_relat_1(A_1)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_86,k6_relat_1(A_1)),'#skF_6'(A_86,k6_relat_1(A_1))),k6_relat_1(A_1))
      | k6_relat_1(A_1) = k4_relat_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_326])).

tff(c_741,plain,(
    ! [A_143] :
      ( r2_hidden('#skF_7'(k6_relat_1(A_143),k6_relat_1(A_143)),A_143)
      | ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143)),'#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143))),k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143)
      | ~ v1_relat_1(k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_334])).

tff(c_772,plain,(
    ! [A_143] :
      ( r2_hidden('#skF_7'(k6_relat_1(A_143),k6_relat_1(A_143)),A_143)
      | ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143)),'#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143))),k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_741])).

tff(c_830,plain,(
    ! [A_151] :
      ( r2_hidden('#skF_7'(k6_relat_1(A_151),k6_relat_1(A_151)),A_151)
      | k4_relat_1(k6_relat_1(A_151)) = k6_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_817,c_772])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_548,plain,(
    ! [A_126] :
      ( '#skF_8'(k6_relat_1(A_126),k6_relat_1(A_126)) = '#skF_7'(k6_relat_1(A_126),k6_relat_1(A_126))
      | k4_relat_1(k6_relat_1(A_126)) = k6_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_537,c_476])).

tff(c_22,plain,(
    ! [A_9,B_19] :
      ( r2_hidden(k4_tarski('#skF_6'(A_9,B_19),'#skF_5'(A_9,B_19)),A_9)
      | ~ r2_hidden(k4_tarski('#skF_8'(A_9,B_19),'#skF_7'(A_9,B_19)),A_9)
      | k4_relat_1(A_9) = B_19
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_758,plain,(
    ! [A_143] :
      ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143)),'#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143))),k6_relat_1(A_143))
      | ~ r2_hidden(k4_tarski('#skF_8'(k6_relat_1(A_143),k6_relat_1(A_143)),'#skF_7'(k6_relat_1(A_143),k6_relat_1(A_143))),k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143)
      | ~ v1_relat_1(k6_relat_1(A_143))
      | ~ v1_relat_1(k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_22])).

tff(c_1305,plain,(
    ! [A_193] :
      ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_193),k6_relat_1(A_193)),'#skF_5'(k6_relat_1(A_193),k6_relat_1(A_193))),k6_relat_1(A_193))
      | ~ r2_hidden(k4_tarski('#skF_8'(k6_relat_1(A_193),k6_relat_1(A_193)),'#skF_7'(k6_relat_1(A_193),k6_relat_1(A_193))),k6_relat_1(A_193))
      | k4_relat_1(k6_relat_1(A_193)) = k6_relat_1(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_758])).

tff(c_1755,plain,(
    ! [A_244] :
      ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_244),k6_relat_1(A_244)),'#skF_5'(k6_relat_1(A_244),k6_relat_1(A_244))),k6_relat_1(A_244))
      | ~ r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_244),k6_relat_1(A_244)),'#skF_7'(k6_relat_1(A_244),k6_relat_1(A_244))),k6_relat_1(A_244))
      | k4_relat_1(k6_relat_1(A_244)) = k6_relat_1(A_244)
      | k4_relat_1(k6_relat_1(A_244)) = k6_relat_1(A_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_1305])).

tff(c_1764,plain,(
    ! [A_1] :
      ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_1),k6_relat_1(A_1)),'#skF_5'(k6_relat_1(A_1),k6_relat_1(A_1))),k6_relat_1(A_1))
      | k4_relat_1(k6_relat_1(A_1)) = k6_relat_1(A_1)
      | ~ r2_hidden('#skF_7'(k6_relat_1(A_1),k6_relat_1(A_1)),A_1) ) ),
    inference(resolution,[status(thm)],[c_40,c_1755])).

tff(c_20,plain,(
    ! [A_9,B_19] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_9,B_19),'#skF_6'(A_9,B_19)),B_19)
      | ~ r2_hidden(k4_tarski('#skF_8'(A_9,B_19),'#skF_7'(A_9,B_19)),A_9)
      | k4_relat_1(A_9) = B_19
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_749,plain,(
    ! [A_143] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143)),'#skF_5'(k6_relat_1(A_143),k6_relat_1(A_143))),k6_relat_1(A_143))
      | ~ r2_hidden(k4_tarski('#skF_8'(k6_relat_1(A_143),k6_relat_1(A_143)),'#skF_7'(k6_relat_1(A_143),k6_relat_1(A_143))),k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143)
      | ~ v1_relat_1(k6_relat_1(A_143))
      | ~ v1_relat_1(k6_relat_1(A_143))
      | k4_relat_1(k6_relat_1(A_143)) = k6_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_20])).

tff(c_1321,plain,(
    ! [A_195] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_195),k6_relat_1(A_195)),'#skF_5'(k6_relat_1(A_195),k6_relat_1(A_195))),k6_relat_1(A_195))
      | ~ r2_hidden(k4_tarski('#skF_8'(k6_relat_1(A_195),k6_relat_1(A_195)),'#skF_7'(k6_relat_1(A_195),k6_relat_1(A_195))),k6_relat_1(A_195))
      | k4_relat_1(k6_relat_1(A_195)) = k6_relat_1(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_749])).

tff(c_1851,plain,(
    ! [A_250] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_250),k6_relat_1(A_250)),'#skF_5'(k6_relat_1(A_250),k6_relat_1(A_250))),k6_relat_1(A_250))
      | ~ r2_hidden(k4_tarski('#skF_7'(k6_relat_1(A_250),k6_relat_1(A_250)),'#skF_7'(k6_relat_1(A_250),k6_relat_1(A_250))),k6_relat_1(A_250))
      | k4_relat_1(k6_relat_1(A_250)) = k6_relat_1(A_250)
      | k4_relat_1(k6_relat_1(A_250)) = k6_relat_1(A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_1321])).

tff(c_1861,plain,(
    ! [A_251] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1(A_251),k6_relat_1(A_251)),'#skF_5'(k6_relat_1(A_251),k6_relat_1(A_251))),k6_relat_1(A_251))
      | k4_relat_1(k6_relat_1(A_251)) = k6_relat_1(A_251)
      | ~ r2_hidden('#skF_7'(k6_relat_1(A_251),k6_relat_1(A_251)),A_251) ) ),
    inference(resolution,[status(thm)],[c_40,c_1851])).

tff(c_1876,plain,(
    ! [A_252] :
      ( k4_relat_1(k6_relat_1(A_252)) = k6_relat_1(A_252)
      | ~ r2_hidden('#skF_7'(k6_relat_1(A_252),k6_relat_1(A_252)),A_252) ) ),
    inference(resolution,[status(thm)],[c_1764,c_1861])).

tff(c_1886,plain,(
    ! [A_151] : k4_relat_1(k6_relat_1(A_151)) = k6_relat_1(A_151) ),
    inference(resolution,[status(thm)],[c_830,c_1876])).

tff(c_34,plain,(
    k4_relat_1(k6_relat_1('#skF_9')) != k6_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1886,c_34])).

%------------------------------------------------------------------------------
