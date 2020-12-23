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
% DateTime   : Thu Dec  3 09:59:30 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 217 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 533 expanded)
%              Number of equality atoms :   14 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_11 > #skF_6 > #skF_5 > #skF_3 > #skF_14 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( v1_relat_1(D)
       => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
        <=> ( r2_hidden(B,C)
            & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

tff(f_62,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_50,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_42,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    ! [A_110] : v1_relat_1(k6_relat_1(A_110)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [A_108,B_109] :
      ( v1_relat_1(k5_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | r2_hidden('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75,plain,(
    r2_hidden('#skF_12','#skF_13') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_215,plain,(
    ! [A_152,B_150,F_149,E_148,D_151] :
      ( r2_hidden(k4_tarski(D_151,E_148),k5_relat_1(A_152,B_150))
      | ~ r2_hidden(k4_tarski(F_149,E_148),B_150)
      | ~ r2_hidden(k4_tarski(D_151,F_149),A_152)
      | ~ v1_relat_1(k5_relat_1(A_152,B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_227,plain,(
    ! [D_151,D_8,A_152,A_1] :
      ( r2_hidden(k4_tarski(D_151,D_8),k5_relat_1(A_152,k6_relat_1(A_1)))
      | ~ r2_hidden(k4_tarski(D_151,D_8),A_152)
      | ~ v1_relat_1(k5_relat_1(A_152,k6_relat_1(A_1)))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(A_152)
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(resolution,[status(thm)],[c_60,c_215])).

tff(c_244,plain,(
    ! [D_155,D_156,A_157,A_158] :
      ( r2_hidden(k4_tarski(D_155,D_156),k5_relat_1(A_157,k6_relat_1(A_158)))
      | ~ r2_hidden(k4_tarski(D_155,D_156),A_157)
      | ~ v1_relat_1(k5_relat_1(A_157,k6_relat_1(A_158)))
      | ~ v1_relat_1(A_157)
      | ~ r2_hidden(D_156,A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_227])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14')
    | ~ r2_hidden('#skF_12','#skF_13')
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,
    ( ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14')
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_44])).

tff(c_79,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_249,plain,
    ( ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14')
    | ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | ~ v1_relat_1('#skF_14')
    | ~ r2_hidden('#skF_12','#skF_13') ),
    inference(resolution,[status(thm)],[c_244,c_79])).

tff(c_253,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_76,c_249])).

tff(c_256,plain,
    ( ~ v1_relat_1(k6_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_38,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_256])).

tff(c_261,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_261])).

tff(c_266,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_265,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_405,plain,(
    ! [A_191,B_189,F_188,D_190,E_187] :
      ( r2_hidden(k4_tarski(D_190,E_187),k5_relat_1(A_191,B_189))
      | ~ r2_hidden(k4_tarski(F_188,E_187),B_189)
      | ~ r2_hidden(k4_tarski(D_190,F_188),A_191)
      | ~ v1_relat_1(k5_relat_1(A_191,B_189))
      | ~ v1_relat_1(B_189)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_424,plain,(
    ! [D_190,A_191] :
      ( r2_hidden(k4_tarski(D_190,'#skF_12'),k5_relat_1(A_191,k5_relat_1('#skF_14',k6_relat_1('#skF_13'))))
      | ~ r2_hidden(k4_tarski(D_190,'#skF_11'),A_191)
      | ~ v1_relat_1(k5_relat_1(A_191,k5_relat_1('#skF_14',k6_relat_1('#skF_13'))))
      | ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
      | ~ v1_relat_1(A_191) ) ),
    inference(resolution,[status(thm)],[c_265,c_405])).

tff(c_428,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_431,plain,
    ( ~ v1_relat_1(k6_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_38,c_428])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_431])).

tff(c_437,plain,(
    v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_540,plain,(
    ! [E_212,B_213,D_214,A_215] :
      ( r2_hidden(k4_tarski('#skF_5'(E_212,B_213,D_214,A_215,k5_relat_1(A_215,B_213)),E_212),B_213)
      | ~ r2_hidden(k4_tarski(D_214,E_212),k5_relat_1(A_215,B_213))
      | ~ v1_relat_1(k5_relat_1(A_215,B_213))
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_557,plain,(
    ! [E_212,A_1,D_214,A_215] :
      ( '#skF_5'(E_212,k6_relat_1(A_1),D_214,A_215,k5_relat_1(A_215,k6_relat_1(A_1))) = E_212
      | ~ r2_hidden(k4_tarski(D_214,E_212),k5_relat_1(A_215,k6_relat_1(A_1)))
      | ~ v1_relat_1(k5_relat_1(A_215,k6_relat_1(A_1)))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(A_215) ) ),
    inference(resolution,[status(thm)],[c_540,c_58])).

tff(c_604,plain,(
    ! [E_220,A_221,D_222,A_223] :
      ( '#skF_5'(E_220,k6_relat_1(A_221),D_222,A_223,k5_relat_1(A_223,k6_relat_1(A_221))) = E_220
      | ~ r2_hidden(k4_tarski(D_222,E_220),k5_relat_1(A_223,k6_relat_1(A_221)))
      | ~ v1_relat_1(k5_relat_1(A_223,k6_relat_1(A_221)))
      | ~ v1_relat_1(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_557])).

tff(c_623,plain,
    ( '#skF_5'('#skF_12',k6_relat_1('#skF_13'),'#skF_11','#skF_14',k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) = '#skF_12'
    | ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_265,c_604])).

tff(c_632,plain,(
    '#skF_5'('#skF_12',k6_relat_1('#skF_13'),'#skF_11','#skF_14',k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_437,c_623])).

tff(c_36,plain,(
    ! [D_100,E_101,B_61,A_9] :
      ( r2_hidden(k4_tarski(D_100,'#skF_5'(E_101,B_61,D_100,A_9,k5_relat_1(A_9,B_61))),A_9)
      | ~ r2_hidden(k4_tarski(D_100,E_101),k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_639,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14')
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | ~ v1_relat_1(k6_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_36])).

tff(c_645,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_437,c_265,c_639])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_645])).

tff(c_649,plain,(
    ~ r2_hidden('#skF_12','#skF_13') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_648,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_828,plain,(
    ! [E_263,B_264,D_265,A_266] :
      ( r2_hidden(k4_tarski('#skF_5'(E_263,B_264,D_265,A_266,k5_relat_1(A_266,B_264)),E_263),B_264)
      | ~ r2_hidden(k4_tarski(D_265,E_263),k5_relat_1(A_266,B_264))
      | ~ v1_relat_1(k5_relat_1(A_266,B_264))
      | ~ v1_relat_1(B_264)
      | ~ v1_relat_1(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_838,plain,(
    ! [E_263,A_1,D_265,A_266] :
      ( '#skF_5'(E_263,k6_relat_1(A_1),D_265,A_266,k5_relat_1(A_266,k6_relat_1(A_1))) = E_263
      | ~ r2_hidden(k4_tarski(D_265,E_263),k5_relat_1(A_266,k6_relat_1(A_1)))
      | ~ v1_relat_1(k5_relat_1(A_266,k6_relat_1(A_1)))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(A_266) ) ),
    inference(resolution,[status(thm)],[c_828,c_58])).

tff(c_846,plain,(
    ! [E_267,A_268,D_269,A_270] :
      ( '#skF_5'(E_267,k6_relat_1(A_268),D_269,A_270,k5_relat_1(A_270,k6_relat_1(A_268))) = E_267
      | ~ r2_hidden(k4_tarski(D_269,E_267),k5_relat_1(A_270,k6_relat_1(A_268)))
      | ~ v1_relat_1(k5_relat_1(A_270,k6_relat_1(A_268)))
      | ~ v1_relat_1(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_838])).

tff(c_862,plain,
    ( '#skF_5'('#skF_12',k6_relat_1('#skF_13'),'#skF_11','#skF_14',k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) = '#skF_12'
    | ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_648,c_846])).

tff(c_870,plain,
    ( '#skF_5'('#skF_12',k6_relat_1('#skF_13'),'#skF_11','#skF_14',k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) = '#skF_12'
    | ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_862])).

tff(c_893,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(splitLeft,[status(thm)],[c_870])).

tff(c_896,plain,
    ( ~ v1_relat_1(k6_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_38,c_893])).

tff(c_900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_896])).

tff(c_902,plain,(
    v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) ),
    inference(splitRight,[status(thm)],[c_870])).

tff(c_901,plain,(
    '#skF_5'('#skF_12',k6_relat_1('#skF_13'),'#skF_11','#skF_14',k5_relat_1('#skF_14',k6_relat_1('#skF_13'))) = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_870])).

tff(c_34,plain,(
    ! [E_101,B_61,D_100,A_9] :
      ( r2_hidden(k4_tarski('#skF_5'(E_101,B_61,D_100,A_9,k5_relat_1(A_9,B_61)),E_101),B_61)
      | ~ r2_hidden(k4_tarski(D_100,E_101),k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_915,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_12'),k6_relat_1('#skF_13'))
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | ~ v1_relat_1(k5_relat_1('#skF_14',k6_relat_1('#skF_13')))
    | ~ v1_relat_1(k6_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_34])).

tff(c_921,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_12'),k6_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_902,c_648,c_915])).

tff(c_18,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_932,plain,(
    r2_hidden('#skF_12','#skF_13') ),
    inference(resolution,[status(thm)],[c_921,c_56])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_932])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:34:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.50  %$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_11 > #skF_6 > #skF_5 > #skF_3 > #skF_14 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10
% 3.06/1.50  
% 3.06/1.50  %Foreground sorts:
% 3.06/1.50  
% 3.06/1.50  
% 3.06/1.50  %Background operators:
% 3.06/1.50  
% 3.06/1.50  
% 3.06/1.50  %Foreground operators:
% 3.06/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.50  tff('#skF_11', type, '#skF_11': $i).
% 3.06/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.06/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.06/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.06/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 3.06/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.06/1.50  tff('#skF_14', type, '#skF_14': $i).
% 3.06/1.50  tff('#skF_13', type, '#skF_13': $i).
% 3.06/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.06/1.50  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.06/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.06/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.50  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.06/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.50  tff('#skF_12', type, '#skF_12': $i).
% 3.06/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.06/1.50  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.06/1.50  
% 3.28/1.51  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_relat_1)).
% 3.28/1.51  tff(f_62, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.28/1.51  tff(f_60, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.28/1.51  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 3.28/1.51  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.28/1.51  tff(c_50, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.51  tff(c_76, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14')), inference(splitLeft, [status(thm)], [c_50])).
% 3.28/1.51  tff(c_42, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.51  tff(c_40, plain, (![A_110]: (v1_relat_1(k6_relat_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.28/1.51  tff(c_38, plain, (![A_108, B_109]: (v1_relat_1(k5_relat_1(A_108, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.51  tff(c_54, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | r2_hidden('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.51  tff(c_75, plain, (r2_hidden('#skF_12', '#skF_13')), inference(splitLeft, [status(thm)], [c_54])).
% 3.28/1.51  tff(c_14, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.28/1.51  tff(c_60, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 3.28/1.51  tff(c_215, plain, (![A_152, B_150, F_149, E_148, D_151]: (r2_hidden(k4_tarski(D_151, E_148), k5_relat_1(A_152, B_150)) | ~r2_hidden(k4_tarski(F_149, E_148), B_150) | ~r2_hidden(k4_tarski(D_151, F_149), A_152) | ~v1_relat_1(k5_relat_1(A_152, B_150)) | ~v1_relat_1(B_150) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.51  tff(c_227, plain, (![D_151, D_8, A_152, A_1]: (r2_hidden(k4_tarski(D_151, D_8), k5_relat_1(A_152, k6_relat_1(A_1))) | ~r2_hidden(k4_tarski(D_151, D_8), A_152) | ~v1_relat_1(k5_relat_1(A_152, k6_relat_1(A_1))) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(A_152) | ~r2_hidden(D_8, A_1))), inference(resolution, [status(thm)], [c_60, c_215])).
% 3.28/1.51  tff(c_244, plain, (![D_155, D_156, A_157, A_158]: (r2_hidden(k4_tarski(D_155, D_156), k5_relat_1(A_157, k6_relat_1(A_158))) | ~r2_hidden(k4_tarski(D_155, D_156), A_157) | ~v1_relat_1(k5_relat_1(A_157, k6_relat_1(A_158))) | ~v1_relat_1(A_157) | ~r2_hidden(D_156, A_158))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_227])).
% 3.28/1.51  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14') | ~r2_hidden('#skF_12', '#skF_13') | ~r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.51  tff(c_78, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14') | ~r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_44])).
% 3.28/1.51  tff(c_79, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(splitLeft, [status(thm)], [c_78])).
% 3.28/1.51  tff(c_249, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14') | ~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1('#skF_14') | ~r2_hidden('#skF_12', '#skF_13')), inference(resolution, [status(thm)], [c_244, c_79])).
% 3.28/1.51  tff(c_253, plain, (~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_76, c_249])).
% 3.28/1.51  tff(c_256, plain, (~v1_relat_1(k6_relat_1('#skF_13')) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_38, c_253])).
% 3.28/1.51  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_256])).
% 3.28/1.51  tff(c_261, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14')), inference(splitRight, [status(thm)], [c_78])).
% 3.28/1.51  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_261])).
% 3.28/1.51  tff(c_266, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14')), inference(splitRight, [status(thm)], [c_50])).
% 3.28/1.51  tff(c_265, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(splitRight, [status(thm)], [c_50])).
% 3.28/1.51  tff(c_405, plain, (![A_191, B_189, F_188, D_190, E_187]: (r2_hidden(k4_tarski(D_190, E_187), k5_relat_1(A_191, B_189)) | ~r2_hidden(k4_tarski(F_188, E_187), B_189) | ~r2_hidden(k4_tarski(D_190, F_188), A_191) | ~v1_relat_1(k5_relat_1(A_191, B_189)) | ~v1_relat_1(B_189) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.51  tff(c_424, plain, (![D_190, A_191]: (r2_hidden(k4_tarski(D_190, '#skF_12'), k5_relat_1(A_191, k5_relat_1('#skF_14', k6_relat_1('#skF_13')))) | ~r2_hidden(k4_tarski(D_190, '#skF_11'), A_191) | ~v1_relat_1(k5_relat_1(A_191, k5_relat_1('#skF_14', k6_relat_1('#skF_13')))) | ~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1(A_191))), inference(resolution, [status(thm)], [c_265, c_405])).
% 3.28/1.51  tff(c_428, plain, (~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(splitLeft, [status(thm)], [c_424])).
% 3.28/1.51  tff(c_431, plain, (~v1_relat_1(k6_relat_1('#skF_13')) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_38, c_428])).
% 3.28/1.51  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_431])).
% 3.28/1.51  tff(c_437, plain, (v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(splitRight, [status(thm)], [c_424])).
% 3.28/1.51  tff(c_540, plain, (![E_212, B_213, D_214, A_215]: (r2_hidden(k4_tarski('#skF_5'(E_212, B_213, D_214, A_215, k5_relat_1(A_215, B_213)), E_212), B_213) | ~r2_hidden(k4_tarski(D_214, E_212), k5_relat_1(A_215, B_213)) | ~v1_relat_1(k5_relat_1(A_215, B_213)) | ~v1_relat_1(B_213) | ~v1_relat_1(A_215))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.51  tff(c_16, plain, (![D_8, C_7, A_1]: (D_8=C_7 | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.28/1.51  tff(c_58, plain, (![D_8, C_7, A_1]: (D_8=C_7 | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 3.28/1.51  tff(c_557, plain, (![E_212, A_1, D_214, A_215]: ('#skF_5'(E_212, k6_relat_1(A_1), D_214, A_215, k5_relat_1(A_215, k6_relat_1(A_1)))=E_212 | ~r2_hidden(k4_tarski(D_214, E_212), k5_relat_1(A_215, k6_relat_1(A_1))) | ~v1_relat_1(k5_relat_1(A_215, k6_relat_1(A_1))) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(A_215))), inference(resolution, [status(thm)], [c_540, c_58])).
% 3.28/1.51  tff(c_604, plain, (![E_220, A_221, D_222, A_223]: ('#skF_5'(E_220, k6_relat_1(A_221), D_222, A_223, k5_relat_1(A_223, k6_relat_1(A_221)))=E_220 | ~r2_hidden(k4_tarski(D_222, E_220), k5_relat_1(A_223, k6_relat_1(A_221))) | ~v1_relat_1(k5_relat_1(A_223, k6_relat_1(A_221))) | ~v1_relat_1(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_557])).
% 3.28/1.51  tff(c_623, plain, ('#skF_5'('#skF_12', k6_relat_1('#skF_13'), '#skF_11', '#skF_14', k5_relat_1('#skF_14', k6_relat_1('#skF_13')))='#skF_12' | ~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_265, c_604])).
% 3.28/1.51  tff(c_632, plain, ('#skF_5'('#skF_12', k6_relat_1('#skF_13'), '#skF_11', '#skF_14', k5_relat_1('#skF_14', k6_relat_1('#skF_13')))='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_437, c_623])).
% 3.28/1.51  tff(c_36, plain, (![D_100, E_101, B_61, A_9]: (r2_hidden(k4_tarski(D_100, '#skF_5'(E_101, B_61, D_100, A_9, k5_relat_1(A_9, B_61))), A_9) | ~r2_hidden(k4_tarski(D_100, E_101), k5_relat_1(A_9, B_61)) | ~v1_relat_1(k5_relat_1(A_9, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.51  tff(c_639, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14') | ~r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1(k6_relat_1('#skF_13')) | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_632, c_36])).
% 3.28/1.51  tff(c_645, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_437, c_265, c_639])).
% 3.28/1.51  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_645])).
% 3.28/1.51  tff(c_649, plain, (~r2_hidden('#skF_12', '#skF_13')), inference(splitRight, [status(thm)], [c_54])).
% 3.28/1.51  tff(c_648, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(splitRight, [status(thm)], [c_54])).
% 3.28/1.51  tff(c_828, plain, (![E_263, B_264, D_265, A_266]: (r2_hidden(k4_tarski('#skF_5'(E_263, B_264, D_265, A_266, k5_relat_1(A_266, B_264)), E_263), B_264) | ~r2_hidden(k4_tarski(D_265, E_263), k5_relat_1(A_266, B_264)) | ~v1_relat_1(k5_relat_1(A_266, B_264)) | ~v1_relat_1(B_264) | ~v1_relat_1(A_266))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.51  tff(c_838, plain, (![E_263, A_1, D_265, A_266]: ('#skF_5'(E_263, k6_relat_1(A_1), D_265, A_266, k5_relat_1(A_266, k6_relat_1(A_1)))=E_263 | ~r2_hidden(k4_tarski(D_265, E_263), k5_relat_1(A_266, k6_relat_1(A_1))) | ~v1_relat_1(k5_relat_1(A_266, k6_relat_1(A_1))) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(A_266))), inference(resolution, [status(thm)], [c_828, c_58])).
% 3.28/1.51  tff(c_846, plain, (![E_267, A_268, D_269, A_270]: ('#skF_5'(E_267, k6_relat_1(A_268), D_269, A_270, k5_relat_1(A_270, k6_relat_1(A_268)))=E_267 | ~r2_hidden(k4_tarski(D_269, E_267), k5_relat_1(A_270, k6_relat_1(A_268))) | ~v1_relat_1(k5_relat_1(A_270, k6_relat_1(A_268))) | ~v1_relat_1(A_270))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_838])).
% 3.28/1.51  tff(c_862, plain, ('#skF_5'('#skF_12', k6_relat_1('#skF_13'), '#skF_11', '#skF_14', k5_relat_1('#skF_14', k6_relat_1('#skF_13')))='#skF_12' | ~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_648, c_846])).
% 3.28/1.51  tff(c_870, plain, ('#skF_5'('#skF_12', k6_relat_1('#skF_13'), '#skF_11', '#skF_14', k5_relat_1('#skF_14', k6_relat_1('#skF_13')))='#skF_12' | ~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_862])).
% 3.28/1.51  tff(c_893, plain, (~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(splitLeft, [status(thm)], [c_870])).
% 3.28/1.51  tff(c_896, plain, (~v1_relat_1(k6_relat_1('#skF_13')) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_38, c_893])).
% 3.28/1.51  tff(c_900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_896])).
% 3.28/1.51  tff(c_902, plain, (v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13')))), inference(splitRight, [status(thm)], [c_870])).
% 3.28/1.51  tff(c_901, plain, ('#skF_5'('#skF_12', k6_relat_1('#skF_13'), '#skF_11', '#skF_14', k5_relat_1('#skF_14', k6_relat_1('#skF_13')))='#skF_12'), inference(splitRight, [status(thm)], [c_870])).
% 3.28/1.51  tff(c_34, plain, (![E_101, B_61, D_100, A_9]: (r2_hidden(k4_tarski('#skF_5'(E_101, B_61, D_100, A_9, k5_relat_1(A_9, B_61)), E_101), B_61) | ~r2_hidden(k4_tarski(D_100, E_101), k5_relat_1(A_9, B_61)) | ~v1_relat_1(k5_relat_1(A_9, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.51  tff(c_915, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_12'), k6_relat_1('#skF_13')) | ~r2_hidden(k4_tarski('#skF_11', '#skF_12'), k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1(k5_relat_1('#skF_14', k6_relat_1('#skF_13'))) | ~v1_relat_1(k6_relat_1('#skF_13')) | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_901, c_34])).
% 3.28/1.51  tff(c_921, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_12'), k6_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_902, c_648, c_915])).
% 3.28/1.51  tff(c_18, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.28/1.51  tff(c_56, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 3.28/1.51  tff(c_932, plain, (r2_hidden('#skF_12', '#skF_13')), inference(resolution, [status(thm)], [c_921, c_56])).
% 3.28/1.51  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_932])).
% 3.28/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.51  
% 3.28/1.51  Inference rules
% 3.28/1.51  ----------------------
% 3.28/1.51  #Ref     : 0
% 3.28/1.51  #Sup     : 159
% 3.28/1.51  #Fact    : 0
% 3.28/1.51  #Define  : 0
% 3.28/1.51  #Split   : 5
% 3.28/1.51  #Chain   : 0
% 3.28/1.51  #Close   : 0
% 3.28/1.51  
% 3.28/1.51  Ordering : KBO
% 3.28/1.51  
% 3.28/1.51  Simplification rules
% 3.28/1.51  ----------------------
% 3.28/1.51  #Subsume      : 7
% 3.28/1.51  #Demod        : 111
% 3.28/1.51  #Tautology    : 32
% 3.28/1.51  #SimpNegUnit  : 2
% 3.28/1.51  #BackRed      : 0
% 3.28/1.51  
% 3.28/1.51  #Partial instantiations: 0
% 3.28/1.51  #Strategies tried      : 1
% 3.28/1.51  
% 3.28/1.51  Timing (in seconds)
% 3.28/1.51  ----------------------
% 3.28/1.52  Preprocessing        : 0.32
% 3.28/1.52  Parsing              : 0.15
% 3.28/1.52  CNF conversion       : 0.03
% 3.28/1.52  Main loop            : 0.42
% 3.28/1.52  Inferencing          : 0.17
% 3.28/1.52  Reduction            : 0.11
% 3.28/1.52  Demodulation         : 0.08
% 3.28/1.52  BG Simplification    : 0.03
% 3.28/1.52  Subsumption          : 0.08
% 3.28/1.52  Abstraction          : 0.03
% 3.28/1.52  MUC search           : 0.00
% 3.28/1.52  Cooper               : 0.00
% 3.28/1.52  Total                : 0.77
% 3.28/1.52  Index Insertion      : 0.00
% 3.28/1.52  Index Deletion       : 0.00
% 3.28/1.52  Index Matching       : 0.00
% 3.28/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
