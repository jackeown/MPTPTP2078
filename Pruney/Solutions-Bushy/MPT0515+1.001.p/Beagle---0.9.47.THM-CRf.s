%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0515+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:25 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 207 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
        <=> ( r2_hidden(A,B)
            & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(k8_relat_1(A_38,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,
    ( r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11')))
    | r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11')))
    | r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_20,plain,(
    ! [A_19,C_34] :
      ( r2_hidden(k4_tarski('#skF_8'(A_19,k2_relat_1(A_19),C_34),C_34),A_19)
      | ~ r2_hidden(C_34,k2_relat_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_153,plain,(
    ! [D_74,E_75,A_76,B_77] :
      ( r2_hidden(k4_tarski(D_74,E_75),k8_relat_1(A_76,B_77))
      | ~ r2_hidden(k4_tarski(D_74,E_75),B_77)
      | ~ r2_hidden(E_75,A_76)
      | ~ v1_relat_1(k8_relat_1(A_76,B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_34,A_19,D_37] :
      ( r2_hidden(C_34,k2_relat_1(A_19))
      | ~ r2_hidden(k4_tarski(D_37,C_34),A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    ! [E_78,A_79,B_80,D_81] :
      ( r2_hidden(E_78,k2_relat_1(k8_relat_1(A_79,B_80)))
      | ~ r2_hidden(k4_tarski(D_81,E_78),B_80)
      | ~ r2_hidden(E_78,A_79)
      | ~ v1_relat_1(k8_relat_1(A_79,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_153,c_22])).

tff(c_183,plain,(
    ! [C_82,A_83,A_84] :
      ( r2_hidden(C_82,k2_relat_1(k8_relat_1(A_83,A_84)))
      | ~ r2_hidden(C_82,A_83)
      | ~ v1_relat_1(k8_relat_1(A_83,A_84))
      | ~ v1_relat_1(A_84)
      | ~ r2_hidden(C_82,k2_relat_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_36])).

tff(c_202,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_183,c_53])).

tff(c_214,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34,c_48,c_202])).

tff(c_218,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_214])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_224,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_223,plain,(
    r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_284,plain,(
    ! [D_103,E_104,B_105,A_106] :
      ( r2_hidden(k4_tarski(D_103,E_104),B_105)
      | ~ r2_hidden(k4_tarski(D_103,E_104),k8_relat_1(A_106,B_105))
      | ~ v1_relat_1(k8_relat_1(A_106,B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_444,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden(k4_tarski('#skF_8'(k8_relat_1(A_135,B_136),k2_relat_1(k8_relat_1(A_135,B_136)),C_137),C_137),B_136)
      | ~ v1_relat_1(k8_relat_1(A_135,B_136))
      | ~ v1_relat_1(B_136)
      | ~ r2_hidden(C_137,k2_relat_1(k8_relat_1(A_135,B_136))) ) ),
    inference(resolution,[status(thm)],[c_20,c_284])).

tff(c_474,plain,(
    ! [C_138,B_139,A_140] :
      ( r2_hidden(C_138,k2_relat_1(B_139))
      | ~ v1_relat_1(k8_relat_1(A_140,B_139))
      | ~ v1_relat_1(B_139)
      | ~ r2_hidden(C_138,k2_relat_1(k8_relat_1(A_140,B_139))) ) ),
    inference(resolution,[status(thm)],[c_444,c_22])).

tff(c_520,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_223,c_474])).

tff(c_534,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_520])).

tff(c_535,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_534])).

tff(c_599,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_535])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_599])).

tff(c_605,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_604,plain,(
    r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_617,plain,(
    ! [E_154,A_155,D_156,B_157] :
      ( r2_hidden(E_154,A_155)
      | ~ r2_hidden(k4_tarski(D_156,E_154),k8_relat_1(A_155,B_157))
      | ~ v1_relat_1(k8_relat_1(A_155,B_157))
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_623,plain,(
    ! [C_158,A_159,B_160] :
      ( r2_hidden(C_158,A_159)
      | ~ v1_relat_1(k8_relat_1(A_159,B_160))
      | ~ v1_relat_1(B_160)
      | ~ r2_hidden(C_158,k2_relat_1(k8_relat_1(A_159,B_160))) ) ),
    inference(resolution,[status(thm)],[c_20,c_617])).

tff(c_634,plain,
    ( r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_604,c_623])).

tff(c_639,plain,
    ( r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_634])).

tff(c_640,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_639])).

tff(c_643,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_640])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_643])).

%------------------------------------------------------------------------------
